#!/usr/bin/env bash
#
# FormalScience 性能基准测试一键运行脚本
#
# 用法:
#   ./run_benchmarks.sh              # 运行所有测试
#   ./run_benchmarks.sh --lean       # 仅运行 Lean 测试
#   ./run_benchmarks.sh --rust       # 仅运行 Rust 测试
#   ./run_benchmarks.sh --python     # 仅运行 Python 测试
#   ./run_benchmarks.sh --compare    # 对比历史基线
#   ./run_benchmarks.sh --json       # 输出 JSON 格式
#

set -e  # 遇到错误立即退出

# ============================================
# 配置
# ============================================

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
RESULTS_DIR="$SCRIPT_DIR/results"
TIMESTAMP=$(date +"%Y%m%d_%H%M%S")
JSON_OUTPUT=false
COMPARE_MODE=false
BASELINE_FILE=""

# 颜色输出
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# ============================================
# 工具函数
# ============================================

log_info() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

log_success() {
    echo -e "${GREEN}[SUCCESS]${NC} $1"
}

log_warn() {
    echo -e "${YELLOW}[WARN]${NC} $1"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

print_header() {
    echo ""
    echo "╔═══════════════════════════════════════════════════════════════╗"
    echo "║     FormalScience 性能基准测试套件                          ║"
    echo "╚═══════════════════════════════════════════════════════════════╝"
    echo ""
    echo "时间戳: $TIMESTAMP"
    echo "工作目录: $SCRIPT_DIR"
    echo ""
}

print_footer() {
    echo ""
    echo "═══════════════════════════════════════════════════════════════"
    echo "✅ 所有基准测试完成!"
    echo "═══════════════════════════════════════════════════════════════"
    echo ""
    echo "结果保存位置: $RESULTS_DIR/${TIMESTAMP}_*.json"
    echo ""
}

# ============================================
# 前置检查
# ============================================

check_prerequisites() {
    log_info "检查前置条件..."
    
    # 创建结果目录
    mkdir -p "$RESULTS_DIR"
    
    # 检查可选依赖
    local lean_available=false
    local rust_available=false
    local python_available=false
    
    if command -v lake &> /dev/null; then
        lean_available=true
        log_success "Lean (lake) 已安装"
    else
        log_warn "Lean (lake) 未安装，跳过 Lean 测试"
    fi
    
    if command -v cargo &> /dev/null; then
        rust_available=true
        log_success "Rust (cargo) 已安装"
    else
        log_warn "Rust (cargo) 未安装，跳过 Rust 测试"
    fi
    
    if command -v python3 &> /dev/null || command -v python &> /dev/null; then
        python_available=true
        log_success "Python 已安装"
    else
        log_warn "Python 未安装，跳过 Python 测试"
    fi
    
    # 返回可用工具状态
    echo "$lean_available $rust_available $python_available"
}

# ============================================
# Lean 测试
# ============================================

run_lean_benchmarks() {
    log_info "运行 Lean 性能测试..."
    
    cd "$SCRIPT_DIR"
    
    # 检查是否存在 lakefile
    if [ -f "../lakefile.lean" ]; then
        cd ..
        
        # 编译项目
        log_info "编译 Lean 项目..."
        if lake build; then
            log_success "Lean 项目编译成功"
            
            # 运行基准测试
            log_info "执行 Lean 基准测试..."
            if lake exe lean_benchmarks 2>&1 | tee "$RESULTS_DIR/${TIMESTAMP}_lean_output.txt"; then
                log_success "Lean 基准测试完成"
            else
                log_error "Lean 基准测试失败"
                return 1
            fi
        else
            log_error "Lean 项目编译失败"
            return 1
        fi
    elif [ -f "lean_benchmarks.lean" ]; then
        # 直接运行 lean 文件
        log_info "直接运行 lean_benchmarks.lean..."
        if lean lean_benchmarks.lean 2>&1 | tee "$RESULTS_DIR/${TIMESTAMP}_lean_output.txt"; then
            log_success "Lean 基准测试完成"
        else
            log_warn "直接运行失败，可能需要配置 lake 环境"
        fi
    else
        log_warn "未找到 Lean 项目配置"
    fi
    
    return 0
}

# ============================================
# Rust 测试
# ============================================

run_rust_benchmarks() {
    log_info "运行 Rust 性能测试..."
    
    cd "$SCRIPT_DIR"
    
    # 检查是否存在 Cargo 项目
    if [ -f "Cargo.toml" ]; then
        log_info "在基准测试目录找到 Rust 项目"
        
        # 运行基准测试
        if cargo run --release 2>&1 | tee "$RESULTS_DIR/${TIMESTAMP}_rust_output.txt"; then
            log_success "Rust 基准测试完成"
        else
            log_error "Rust 基准测试失败"
            return 1
        fi
    elif [ -f "rust_benchmarks.rs" ]; then
        # 尝试直接编译运行
        log_info "直接编译运行 rust_benchmarks.rs..."
        if rustc rust_benchmarks.rs -o /tmp/rust_benchmarks && /tmp/rust_benchmarks 2>&1 | tee "$RESULTS_DIR/${TIMESTAMP}_rust_output.txt"; then
            log_success "Rust 基准测试完成"
        else
            log_warn "直接编译运行失败，可能需要配置 Cargo 项目"
        fi
    else
        log_warn "未找到 Rust 测试文件"
    fi
    
    return 0
}

# ============================================
# Python 测试
# ============================================

run_python_benchmarks() {
    log_info "运行 Python 性能测试..."
    
    cd "$SCRIPT_DIR"
    
    # 确定 Python 命令
    local PYTHON_CMD="python3"
    if ! command -v python3 &> /dev/null; then
        PYTHON_CMD="python"
    fi
    
    if [ -f "python_benchmarks.py" ]; then
        local json_flag=""
        if [ "$JSON_OUTPUT" = true ]; then
            json_flag="--json"
        fi
        
        if $PYTHON_CMD python_benchmarks.py $json_flag --output "$RESULTS_DIR/${TIMESTAMP}_python.json" 2>&1 | tee "$RESULTS_DIR/${TIMESTAMP}_python_output.txt"; then
            log_success "Python 基准测试完成"
        else
            log_error "Python 基准测试失败"
            return 1
        fi
    else
        log_warn "未找到 Python 测试文件"
    fi
    
    return 0
}

# ============================================
# 结果汇总
# ============================================

generate_summary() {
    log_info "生成测试汇总报告..."
    
    local summary_file="$RESULTS_DIR/${TIMESTAMP}_summary.md"
    
    cat > "$summary_file" << EOF
# 性能基准测试汇总报告

**生成时间**: $(date "+%Y-%m-%d %H:%M:%S")

## 执行概况

| 测试类型 | 状态 | 输出文件 |
|---------|------|---------|
| Lean | $([ -f "$RESULTS_DIR/${TIMESTAMP}_lean_output.txt" ] && echo "✅ 完成" || echo "⏭️ 跳过") | ${TIMESTAMP}_lean_output.txt |
| Rust | $([ -f "$RESULTS_DIR/${TIMESTAMP}_rust_output.txt" ] && echo "✅ 完成" || echo "⏭️ 跳过") | ${TIMESTAMP}_rust_output.txt |
| Python | $([ -f "$RESULTS_DIR/${TIMESTAMP}_python_output.txt" ] && echo "✅ 完成" || echo "⏭️ 跳过") | ${TIMESTAMP}_python_output.txt |

## 可用结果文件

$(ls -la "$RESULTS_DIR"/${TIMESTAMP}_* 2>/dev/null | awk '{print "- " $9 " (" $5 " bytes)"}')

## 系统信息

- OS: $(uname -s)
- Kernel: $(uname -r)
- Architecture: $(uname -m)
- CPU: $(cat /proc/cpuinfo 2>/dev/null | grep "model name" | head -1 | cut -d: -f2 | xargs || echo "N/A")
- Memory: $(free -h 2>/dev/null | grep Mem | awk '{print $2}' || echo "N/A")

## 后续步骤

1. 查看详细结果: \`cat $RESULTS_DIR/${TIMESTAMP}_*_output.txt\`
2. 对比历史数据: \`./run_benchmarks.sh --compare\`
3. 更新性能基线: \`cp $RESULTS_DIR/${TIMESTAMP}_*.json baseline/\`

---

*由 run_benchmarks.sh 自动生成*
EOF

    log_success "汇总报告已生成: $summary_file"
}

# ============================================
# 对比模式
# ============================================

compare_with_baseline() {
    log_info "对比历史基线数据..."
    
    if [ -z "$BASELINE_FILE" ]; then
        # 查找最新的基线文件
        BASELINE_FILE=$(ls -t "$RESULTS_DIR"/*_python.json 2>/dev/null | head -1)
    fi
    
    if [ -n "$BASELINE_FILE" ] && [ -f "$BASELINE_FILE" ]; then
        log_info "使用基线文件: $BASELINE_FILE"
        
        # 这里可以添加具体的对比逻辑
        log_warn "对比功能待实现"
    else
        log_warn "未找到基线文件"
    fi
}

# ============================================
# 主程序
# ============================================

main() {
    # 解析参数
    local run_lean=false
    local run_rust=false
    local run_python=false
    local run_all=true
    
    while [[ $# -gt 0 ]]; do
        case $1 in
            --lean)
                run_lean=true
                run_all=false
                shift
                ;;
            --rust)
                run_rust=true
                run_all=false
                shift
                ;;
            --python)
                run_python=true
                run_all=false
                shift
                ;;
            --json)
                JSON_OUTPUT=true
                shift
                ;;
            --compare)
                COMPARE_MODE=true
                shift
                ;;
            --baseline)
                BASELINE_FILE="$2"
                shift 2
                ;;
            -h|--help)
                echo "用法: $0 [选项]"
                echo ""
                echo "选项:"
                echo "  --lean       仅运行 Lean 测试"
                echo "  --rust       仅运行 Rust 测试"
                echo "  --python     仅运行 Python 测试"
                echo "  --json       输出 JSON 格式结果"
                echo "  --compare    对比历史基线数据"
                echo "  --baseline   指定基线文件路径"
                echo "  -h, --help   显示此帮助信息"
                exit 0
                ;;
            *)
                log_error "未知选项: $1"
                exit 1
                ;;
        esac
    done
    
    # 打印标题
    print_header
    
    # 检查前置条件
    read lean_avail rust_avail python_avail <<< "$(check_prerequisites)"
    
    # 运行测试
    local exit_code=0
    
    if [ "$run_all" = true ] || [ "$run_lean" = true ]; then
        if [ "$lean_avail" = true ]; then
            run_lean_benchmarks || exit_code=1
        fi
    fi
    
    if [ "$run_all" = true ] || [ "$run_rust" = true ]; then
        if [ "$rust_avail" = true ]; then
            run_rust_benchmarks || exit_code=1
        fi
    fi
    
    if [ "$run_all" = true ] || [ "$run_python" = true ]; then
        if [ "$python_avail" = true ]; then
            run_python_benchmarks || exit_code=1
        fi
    fi
    
    # 对比模式
    if [ "$COMPARE_MODE" = true ]; then
        compare_with_baseline
    fi
    
    # 生成汇总
    generate_summary
    
    # 打印页脚
    print_footer
    
    exit $exit_code
}

# 运行主程序
main "$@"
