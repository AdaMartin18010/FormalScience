#!/bin/bash
# =============================================================================
# Docker Build Script - FormalScience Project
# =============================================================================
# 功能：构建Docker镜像，支持标签管理和仓库推送
# 用法：./docker_build.sh [options] [tag]
# =============================================================================

set -euo pipefail

# -----------------------------------------------------------------------------
# 配置变量
# -----------------------------------------------------------------------------
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
DOCKER_CONTEXT="${PROJECT_ROOT}"
DOCKERFILE="${PROJECT_ROOT}/docs/Refactor/Dockerfile"

# 镜像配置
IMAGE_NAME="${IMAGE_NAME:-formalscience}"
REGISTRY="${REGISTRY:-}"  # 例如：docker.io/username 或 ghcr.io/username
NAMESPACE="${NAMESPACE:-formalscience}"

# 默认标签
DEFAULT_TAG="latest"
TAG="${1:-$DEFAULT_TAG}"

# 构建参数
BUILD_ARGS=""
NO_CACHE=""
PUSH="false"
PLATFORMS=""
VERBOSE="false"

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

log_debug() {
    if [[ "$VERBOSE" == "true" ]]; then
        echo -e "${CYAN}[DEBUG]${NC} $1"
    fi
}

# -----------------------------------------------------------------------------
# 帮助信息
# -----------------------------------------------------------------------------
show_help() {
    cat << EOF
${BOLD}Docker Build Script for FormalScience${NC}

${BOLD}用法:${NC}
    $(basename "$0") [options] [tag]

${BOLD}参数:${NC}
    tag                     镜像标签 (默认: latest)

${BOLD}选项:${NC}
    -h, --help              显示帮助信息
    -n, --no-cache          不使用缓存构建
    -p, --push              构建后推送到仓库
    -r, --registry REG      指定镜像仓库
    -a, --arg KEY=VALUE     添加构建参数
    --platform PLATFORMS    多平台构建 (如: linux/amd64,linux/arm64)
    -v, --verbose           显示详细输出

${BOLD}示例:${NC}
    # 构建最新版本
    $(basename "$0")

    # 构建指定版本
    $(basename "$0") v1.0.0

    # 无缓存构建
    $(basename "$0") -n v1.0.0

    # 构建并推送
    $(basename "$0") -p v1.0.0

    # 多平台构建并推送
    $(basename "$0") --platform linux/amd64,linux/arm64 -p v1.0.0

    # 指定仓库
    $(basename "$0") -r ghcr.io/username v1.0.0

${BOLD}环境变量:${NC}
    IMAGE_NAME              镜像名称 (默认: formalscience)
    REGISTRY                镜像仓库
    NAMESPACE               命名空间

EOF
}

# -----------------------------------------------------------------------------
# 解析参数
# -----------------------------------------------------------------------------
parse_args() {
    while [[ $# -gt 0 ]]; do
        case $1 in
            -h|--help)
                show_help
                exit 0
                ;;
            -n|--no-cache)
                NO_CACHE="--no-cache"
                shift
                ;;
            -p|--push)
                PUSH="true"
                shift
                ;;
            -r|--registry)
                REGISTRY="$2"
                shift 2
                ;;
            -a|--arg)
                BUILD_ARGS="${BUILD_ARGS} --build-arg $2"
                shift 2
                ;;
            --platform)
                PLATFORMS="$2"
                shift 2
                ;;
            -v|--verbose)
                VERBOSE="true"
                shift
                ;;
            -*)
                log_error "未知选项: $1"
                show_help
                exit 1
                ;;
            *)
                TAG="$1"
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
    
    # 检查Docker是否运行
    if ! docker info &> /dev/null; then
        log_error "Docker 守护进程未运行"
        exit 1
    fi
    
    log_success "依赖检查通过"
}

# -----------------------------------------------------------------------------
# 设置镜像标签
# -----------------------------------------------------------------------------
setup_tags() {
    # 完整镜像名称
    if [[ -n "$REGISTRY" ]]; then
        FULL_IMAGE_NAME="${REGISTRY}/${NAMESPACE}/${IMAGE_NAME}"
    else
        FULL_IMAGE_NAME="${IMAGE_NAME}"
    fi
    
    # 生成额外标签
    TAGS=()
    TAGS+=("${FULL_IMAGE_NAME}:${TAG}")
    
    # 如果是latest，也添加版本标签
    if [[ "$TAG" == "latest" ]]; then
        # 尝试从Git获取版本
        if command -v git &> /dev/null && [[ -d "${PROJECT_ROOT}/.git" ]]; then
            GIT_VERSION=$(git describe --tags --always --dirty 2>/dev/null || echo "")
            if [[ -n "$GIT_VERSION" ]]; then
                TAGS+=("${FULL_IMAGE_NAME}:${GIT_VERSION}")
            fi
        fi
    fi
    
    log_info "镜像标签:"
    for tag in "${TAGS[@]}"; do
        echo "  - $tag"
    done
}

# -----------------------------------------------------------------------------
# 构建镜像
# -----------------------------------------------------------------------------
build_image() {
    log_info "开始构建镜像..."
    log_info "Dockerfile: ${DOCKERFILE}"
    log_info "构建上下文: ${DOCKER_CONTEXT}"
    
    # 准备构建命令
    BUILD_CMD="docker build"
    
    # 添加标签
    for tag in "${TAGS[@]}"; do
        BUILD_CMD="${BUILD_CMD} -t ${tag}"
    done
    
    # 添加其他选项
    if [[ -n "$NO_CACHE" ]]; then
        BUILD_CMD="${BUILD_CMD} ${NO_CACHE}"
        log_info "不使用缓存构建"
    fi
    
    if [[ -n "$BUILD_ARGS" ]]; then
        BUILD_CMD="${BUILD_CMD} ${BUILD_ARGS}"
    fi
    
    # 多平台构建需要buildx
    if [[ -n "$PLATFORMS" ]]; then
        log_info "多平台构建: ${PLATFORMS}"
        
        # 检查buildx
        if ! docker buildx version &> /dev/null; then
            log_error "Docker Buildx 未安装"
            exit 1
        fi
        
        # 创建builder（如果不存在）
        if ! docker buildx inspect formalscience-builder &> /dev/null; then
            log_info "创建 buildx builder..."
            docker buildx create --name formalscience-builder --use
        fi
        
        BUILD_CMD="docker buildx build --platform ${PLATFORMS}"
        
        for tag in "${TAGS[@]}"; do
            BUILD_CMD="${BUILD_CMD} -t ${tag}"
        done
        
        if [[ "$PUSH" == "true" ]]; then
            BUILD_CMD="${BUILD_CMD} --push"
        fi
        
        BUILD_CMD="${BUILD_CMD} --load"
    fi
    
    BUILD_CMD="${BUILD_CMD} -f ${DOCKERFILE} ${DOCKER_CONTEXT}"
    
    log_debug "构建命令: ${BUILD_CMD}"
    
    # 执行构建
    if [[ "$VERBOSE" == "true" ]]; then
        eval "$BUILD_CMD"
    else
        eval "$BUILD_CMD" 2>&1 | while read -r line; do
            echo "  $line"
        done
    fi
    
    if [[ $? -eq 0 ]]; then
        log_success "镜像构建成功"
    else
        log_error "镜像构建失败"
        exit 1
    fi
}

# -----------------------------------------------------------------------------
# 推送镜像
# -----------------------------------------------------------------------------
push_image() {
    if [[ "$PUSH" != "true" ]]; then
        return 0
    fi
    
    log_info "推送镜像到仓库..."
    
    for tag in "${TAGS[@]}"; do
        log_info "推送: $tag"
        if docker push "$tag"; then
            log_success "推送成功: $tag"
        else
            log_error "推送失败: $tag"
            exit 1
        fi
    done
}

# -----------------------------------------------------------------------------
# 显示镜像信息
# -----------------------------------------------------------------------------
show_image_info() {
    log_info "镜像信息:"
    
    for tag in "${TAGS[@]}"; do
        echo ""
        echo "  标签: $tag"
        
        # 获取镜像ID
        IMAGE_ID=$(docker images -q "$tag" 2>/dev/null || echo "N/A")
        echo "  ID: $IMAGE_ID"
        
        # 获取镜像大小
        IMAGE_SIZE=$(docker images --format "{{.Size}}" "$tag" 2>/dev/null || echo "N/A")
        echo "  大小: $IMAGE_SIZE"
        
        # 获取创建时间
        CREATED=$(docker images --format "{{.CreatedAt}}" "$tag" 2>/dev/null || echo "N/A")
        echo "  创建时间: $CREATED"
    done
    
    echo ""
    log_success "构建完成!"
}

# -----------------------------------------------------------------------------
# 主函数
# -----------------------------------------------------------------------------
main() {
    echo -e "${BOLD}============================================${NC}"
    echo -e "${BOLD}  FormalScience Docker Build Script${NC}"
    echo -e "${BOLD}============================================${NC}"
    echo ""
    
    parse_args "$@"
    check_dependencies
    setup_tags
    build_image
    push_image
    show_image_info
}

# 运行主函数
main "$@"
