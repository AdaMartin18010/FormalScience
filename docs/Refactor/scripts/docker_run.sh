#!/bin/bash
# =============================================================================
# Docker Run Script - FormalScience Project
# =============================================================================
# 功能：启动Docker容器，支持卷挂载和交互式运行
# 用法：./docker_run.sh [options] [command]
# =============================================================================

set -euo pipefail

# -----------------------------------------------------------------------------
# 配置变量
# -----------------------------------------------------------------------------
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"

# 默认配置
IMAGE_NAME="${IMAGE_NAME:-formalscience}"
IMAGE_TAG="${IMAGE_TAG:-latest}"
CONTAINER_NAME="${CONTAINER_NAME:-formalscience-run}"

# 端口映射
JUPYTER_PORT="${JUPYTER_PORT:-8888}"
HTTP_PORT="${HTTP_PORT:-8080}"
LEAN_PORT="${LEAN_PORT:-3000}"

# 卷挂载
MOUNT_PROJECT="true"
MOUNT_SSH="true"
MOUNT_GIT="true"

# 运行选项
INTERACTIVE="true"
DETACH="false"
REMOVE="false"
GPU="false"

# -----------------------------------------------------------------------------
# 颜色定义
# -----------------------------------------------------------------------------
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
NC='\033[0m' # No Color
BOLD='\033[1m'

# -----------------------------------------------------------------------------
# 日志函数
# -----------------------------------------------------------------------------
log_info() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

log_success() {
    echo -e "${GREEN}[SUCCESS]${NC} $1"
}

log_warning() {
    echo -e "${YELLOW}[WARNING]${NC} $1"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# -----------------------------------------------------------------------------
# 帮助信息
# -----------------------------------------------------------------------------
show_help() {
    cat << EOF
${BOLD}Docker Run Script for FormalScience${NC}

${BOLD}用法:${NC}
    $(basename "$0") [options] [command]

${BOLD}参数:${NC}
    command                 在容器中执行的命令 (默认: /bin/bash)

${BOLD}选项:${NC}
    -h, --help              显示帮助信息
    -i, --image IMAGE       指定镜像名称 (默认: formalscience:latest)
    -n, --name NAME         指定容器名称 (默认: formalscience-run)
    -d, --detach            后台运行容器
    -r, --rm                容器停止后自动删除
    -p, --ports             映射所有端口
    -j, --jupyter PORT      指定Jupyter端口 (默认: 8888)
    -w, --http PORT         指定HTTP端口 (默认: 8080)
    --no-mount              不挂载项目目录
    --no-ssh                不挂载SSH密钥
    --no-git                不挂载Git配置
    --gpu                   启用GPU支持
    --env KEY=VALUE         设置环境变量
    -v, --volume HOST:CONT  挂载额外卷

${BOLD}示例:${NC}
    # 交互式启动
    $(basename "$0")

    # 后台运行Jupyter
    $(basename "$0") -d -j 8888 "jupyter lab --ip=0.0.0.0"

    # 运行特定命令
    $(basename "$0") "lean --version"

    # 使用特定镜像
    $(basename "$0") -i formalscience:v1.0.0

    # 临时容器，自动删除
    $(basename "$0") -r "python3 script.py"

    # 启用GPU
    $(basename "$0") --gpu "python3 train.py"

${BOLD}环境变量:${NC}
    IMAGE_NAME              镜像名称 (默认: formalscience)
    IMAGE_TAG               镜像标签 (默认: latest)
    CONTAINER_NAME          容器名称 (默认: formalscience-run)
    JUPYTER_PORT            Jupyter端口 (默认: 8888)
    HTTP_PORT               HTTP端口 (默认: 8080)

EOF
}

# -----------------------------------------------------------------------------
# 解析参数
# -----------------------------------------------------------------------------
parse_args() {
    USER_COMMAND=""
    EXTRA_VOLUMES=()
    EXTRA_ENVS=()
    
    while [[ $# -gt 0 ]]; do
        case $1 in
            -h|--help)
                show_help
                exit 0
                ;;
            -i|--image)
                IMAGE_NAME="${2%:*}"
                IMAGE_TAG="${2#*:}"
                shift 2
                ;;
            -n|--name)
                CONTAINER_NAME="$2"
                shift 2
                ;;
            -d|--detach)
                DETACH="true"
                shift
                ;;
            -r|--rm)
                REMOVE="true"
                shift
                ;;
            -p|--ports)
                MOUNT_PORTS="true"
                shift
                ;;
            -j|--jupyter)
                JUPYTER_PORT="$2"
                shift 2
                ;;
            -w|--http)
                HTTP_PORT="$2"
                shift 2
                ;;
            --no-mount)
                MOUNT_PROJECT="false"
                shift
                ;;
            --no-ssh)
                MOUNT_SSH="false"
                shift
                ;;
            --no-git)
                MOUNT_GIT="false"
                shift
                ;;
            --gpu)
                GPU="true"
                shift
                ;;
            --env)
                EXTRA_ENVS+=("$2")
                shift 2
                ;;
            -v|--volume)
                EXTRA_VOLUMES+=("$2")
                shift 2
                ;;
            -*)
                log_error "未知选项: $1"
                show_help
                exit 1
                ;;
            *)
                USER_COMMAND="$1"
                shift
                ;;
        esac
    done
}

# -----------------------------------------------------------------------------
# 检查依赖
# -----------------------------------------------------------------------------
check_dependencies() {
    log_info "检查依赖..."
    
    if ! command -v docker &> /dev/null; then
        log_error "Docker 未安装"
        exit 1
    fi
    
    if ! docker info &> /dev/null; then
        log_error "Docker 守护进程未运行"
        exit 1
    fi
    
    # 检查镜像是否存在
    FULL_IMAGE="${IMAGE_NAME}:${IMAGE_TAG}"
    if ! docker images --format "{{.Repository}}:{{.Tag}}" | grep -q "^${FULL_IMAGE}$"; then
        log_warning "镜像不存在: ${FULL_IMAGE}"
        log_info "请先运行构建脚本: ./docker_build.sh"
        exit 1
    fi
    
    log_success "依赖检查通过"
}

# -----------------------------------------------------------------------------
# 准备运行命令
# -----------------------------------------------------------------------------
prepare_run_command() {
    RUN_CMD="docker run"
    
    # 容器名称
    RUN_CMD="${RUN_CMD} --name ${CONTAINER_NAME}"
    
    # 交互式选项
    if [[ "$INTERACTIVE" == "true" ]]; then
        RUN_CMD="${RUN_CMD} -it"
    fi
    
    # 后台运行
    if [[ "$DETACH" == "true" ]]; then
        RUN_CMD="${RUN_CMD} -d"
    fi
    
    # 自动删除
    if [[ "$REMOVE" == "true" ]]; then
        RUN_CMD="${RUN_CMD} --rm"
    fi
    
    # 端口映射
    RUN_CMD="${RUN_CMD} -p ${JUPYTER_PORT}:8888"
    RUN_CMD="${RUN_CMD} -p ${HTTP_PORT}:8080"
    RUN_CMD="${RUN_CMD} -p ${LEAN_PORT}:3000"
    
    # GPU支持
    if [[ "$GPU" == "true" ]]; then
        if docker run --help | grep -q "--gpus"; then
            RUN_CMD="${RUN_CMD} --gpus all"
            log_info "启用GPU支持"
        else
            log_warning "Docker不支持--gpus选项，跳过GPU配置"
        fi
    fi
    
    # 卷挂载 - 项目目录
    if [[ "$MOUNT_PROJECT" == "true" ]]; then
        RUN_CMD="${RUN_CMD} -v ${PROJECT_ROOT}:/workspace:cached"
        log_info "挂载项目目录: ${PROJECT_ROOT} -> /workspace"
    fi
    
    # 卷挂载 - SSH密钥
    if [[ "$MOUNT_SSH" == "true" ]] && [[ -d "$HOME/.ssh" ]]; then
        RUN_CMD="${RUN_CMD} -v ${HOME}/.ssh:/root/.ssh:ro"
        log_info "挂载SSH密钥"
    fi
    
    # 卷挂载 - Git配置
    if [[ "$MOUNT_GIT" == "true" ]] && [[ -f "$HOME/.gitconfig" ]]; then
        RUN_CMD="${RUN_CMD} -v ${HOME}/.gitconfig:/root/.gitconfig:ro"
        log_info "挂载Git配置"
    fi
    
    # 额外卷挂载
    for vol in "${EXTRA_VOLUMES[@]}"; do
        RUN_CMD="${RUN_CMD} -v ${vol}"
        log_info "挂载额外卷: ${vol}"
    done
    
    # 环境变量
    RUN_CMD="${RUN_CMD} -e TZ=Asia/Shanghai"
    RUN_CMD="${RUN_CMD} -e PYTHONPATH=/workspace"
    RUN_CMD="${RUN_CMD} -e RUST_LOG=debug"
    
    for env in "${EXTRA_ENVS[@]}"; do
        RUN_CMD="${RUN_CMD} -e ${env}"
    done
    
    # 工作目录
    RUN_CMD="${RUN_CMD} -w /workspace"
    
    # 镜像名称
    RUN_CMD="${RUN_CMD} ${IMAGE_NAME}:${IMAGE_TAG}"
    
    # 用户命令
    if [[ -n "$USER_COMMAND" ]]; then
        RUN_CMD="${RUN_CMD} ${USER_COMMAND}"
    else
        RUN_CMD="${RUN_CMD} /bin/bash"
    fi
}

# -----------------------------------------------------------------------------
# 运行容器
# -----------------------------------------------------------------------------
run_container() {
    log_info "启动容器..."
    log_info "容器名称: ${CONTAINER_NAME}"
    log_info "镜像: ${IMAGE_NAME}:${IMAGE_TAG}"
    
    # 检查同名容器是否存在
    if docker ps -a --format "{{.Names}}" | grep -q "^${CONTAINER_NAME}$"; then
        log_warning "容器 ${CONTAINER_NAME} 已存在"
        
        # 检查是否在运行
        if docker ps --format "{{.Names}}" | grep -q "^${CONTAINER_NAME}$"; then
            log_info "容器正在运行，进入容器..."
            docker exec -it "${CONTAINER_NAME}" /bin/bash
            exit 0
        else
            log_info "启动已存在的容器..."
            docker start -i "${CONTAINER_NAME}"
            exit 0
        fi
    fi
    
    log_info "执行命令: ${RUN_CMD}"
    echo ""
    
    eval "$RUN_CMD"
}

# -----------------------------------------------------------------------------
# 显示容器信息
# -----------------------------------------------------------------------------
show_container_info() {
    echo ""
    log_success "容器操作完成!"
    
    if [[ "$DETACH" == "true" ]]; then
        echo ""
        log_info "容器信息:"
        docker ps --filter "name=${CONTAINER_NAME}" --format "  名称: {{.Names}}\n  状态: {{.Status}}\n  端口: {{.Ports}}"
        
        echo ""
        log_info "常用命令:"
        echo "  查看日志: docker logs -f ${CONTAINER_NAME}"
        echo "  进入容器: docker exec -it ${CONTAINER_NAME} /bin/bash"
        echo "  停止容器: docker stop ${CONTAINER_NAME}"
        echo "  删除容器: docker rm ${CONTAINER_NAME}"
        
        # 显示Jupyter链接
        if [[ -n "$JUPYTER_PORT" ]]; then
            echo ""
            log_info "Jupyter Notebook: http://localhost:${JUPYTER_PORT}"
        fi
    fi
}

# -----------------------------------------------------------------------------
# 主函数
# -----------------------------------------------------------------------------
main() {
    echo -e "${BOLD}============================================${NC}"
    echo -e "${BOLD}  FormalScience Docker Run Script${NC}"
    echo -e "${BOLD}============================================${NC}"
    echo ""
    
    parse_args "$@"
    check_dependencies
    prepare_run_command
    run_container
    show_container_info
}

# 运行主函数
main "$@"
