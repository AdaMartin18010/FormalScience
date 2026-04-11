#!/bin/bash
#
# FormalScience 一键测试脚本 (Linux/Mac)
#
# 功能: 运行所有测试并生成综合报告
#
# 使用方法:
#   chmod +x run_all.sh
#   ./run_all.sh [options]
#
# 选项:
#   --lean-only     只运行 Lean 测试
#   --rust-only     只运行 Rust 测试
#   --md-only       只运行 Markdown 验证
#   --coverage      生成覆盖率报告
#   --ci            CI 模式 (非交互式)
#

set -e  # 遇到错误立即退出

# 颜色定义
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
NC='\033[0m' # No Color

# 脚本目录
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TESTS_DIR="$SCRIPT_DIR"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../../../.." && pwd)"

# 计数器
TESTS_PASSED=0
TESTS_FAILED=0
TEST_RESULTS=()

# 解析参数
LEAN_ONLY=false
RUST_ONLY=false
MD_ONLY=false
GENERATE_COVERAGE=false
CI_MODE=false

while [[ $# -gt 0 ]]; do
    case $1 in
        --lean-only)
            LEAN_ONLY=true
            shift
            ;;
        --rust-only)
            RUST_ONLY=true
            shift
            ;;
        --md-only)
            MD_ONLY=true
            shift
            ;;
        --coverage)
            GENERATE_COVERAGE=true
            shift
            ;;
        --ci)
            CI_MODE=true
            shift
            ;;
        --help|-h)
            echo "FormalScience 测试脚本"
            echo ""
            echo "选项:"
            echo "  --lean-only     只运行 Lean 测试"
            echo "  --rust-only     只运行 Rust 测试"
            echo "  --md-only       只运行 Markdown 验证"
            echo "  --coverage      生成覆盖率报告"
            echo "  --ci            CI 模式 (非交互式)"
            echo "  --help, -h      显示帮助"
            exit 0
            ;;
        *)
            echo "未知选项: $1"
            exit 1
            ;;
    esac
done

# 确定运行哪些测试
RUN_LEAN=true
RUN_RUST=true
RUN_MD=true

if $LEAN_ONLY; then
    RUN_RUST=false
    RUN_MD=false
fi

if $RUST_ONLY; then
    RUN_LEAN=false
    RUN_MD=false
fi

if $MD_ONLY; then
    RUN_LEAN=false
    RUN_RUST=false
fi

# 打印标题
print_header() {
    echo ""
    echo -e "${CYAN}╔══════════════════════════════════════════════════════════╗${NC}"
    echo -e "${CYAN}║       FormalScience 综合测试套件                        ║${NC}"
    echo -e "${CYAN}╚══════════════════════════════════════════════════════════╝${NC}"
    echo ""
    echo -e "${BLUE}项目路径:${NC} $PROJECT_ROOT"
    echo -e "${BLUE}测试路径:${NC} $TESTS_DIR"
    echo -e "${BLUE}运行时间:${NC} $(date '+%Y-%m-%d %H:%M:%S')"
    echo ""
}

# 运行测试并记录结果
run_test() {
    local test_name="$1"
    local test_cmd="$2"
    
    echo -e "${YELLOW}▶ 运行: $test_name${NC}"
    echo "  命令: $test_cmd"
    echo ""
    
    if eval "$test_cmd"; then
        echo -e "${GREEN}✅ $test_name 通过${NC}"
        TESTS_PASSED=$((TESTS_PASSED + 1))
        TEST_RESULTS+=("✅ $test_name")
        return 0
    else
        echo -e "${RED}❌ $test_name 失败${NC}"
        TESTS_FAILED=$((TESTS_FAILED + 1))
        TEST_RESULTS+=("❌ $test_name")
        return 1
    fi
}

# 检查依赖
check_dependencies() {
    echo -e "${CYAN}📋 检查依赖...${NC}"
    
    local missing_deps=()
    
    if $RUN_LEAN && ! command -v lean &> /dev/null; then
        missing_deps+=("Lean")
    fi
    
    if $RUN_RUST && ! command -v cargo &> /dev/null; then
        missing_deps+=("Rust/Cargo")
    fi
    
    if $RUN_MD && ! command -v python3 &> /dev/null; then
        missing_deps+=("Python3")
    fi
    
    if [ ${#missing_deps[@]} -gt 0 ]; then
        echo -e "${YELLOW}⚠️  缺少依赖:${NC}"
        for dep in "${missing_deps[@]}"; do
            echo "  - $dep"
        done
        echo ""
        
        if ! $CI_MODE; then
            read -p "是否继续? (y/N) " -n 1 -r
            echo
            if [[ ! $REPLY =~ ^[Yy]$ ]]; then
                exit 1
            fi
        fi
    else
        echo -e "${GREEN}✅ 所有依赖已安装${NC}"
    fi
    echo ""
}

# Lean 测试
run_lean_tests() {
    if ! $RUN_LEAN; then
        return 0
    fi
    
    echo -e "${CYAN}══════════════════════════════════════════════════════════${NC}"
    echo -e "${CYAN}                  Lean 测试${NC}"
    echo -e "${CYAN}══════════════════════════════════════════════════════════${NC}"
    echo ""
    
    cd "$TESTS_DIR"
    
    # 检查 lean_tests.lean
    if [ -f "lean_tests.lean" ]; then
        run_test "Lean 测试套件" "lean --run lean_tests.lean"
    else
        echo -e "${YELLOW}⚠️  lean_tests.lean 不存在${NC}"
    fi
    
    # 验证示例文件
    local lean_examples_dir="$PROJECT_ROOT/docs/Refactor/examples/lean"
    if [ -d "$lean_examples_dir" ]; then
        echo ""
        echo -e "${BLUE}验证 Lean 示例文件...${NC}"
        
        for file in "$lean_examples_dir"/*.lean; do
            if [ -f "$file" ]; then
                local basename=$(basename "$file")
                echo -n "  检查 $basename... "
                
                if lean "$file" 2>/dev/null; then
                    echo -e "${GREEN}✓${NC}"
                else
                    echo -e "${YELLOW}⚠ (语法检查未完成)${NC}"
                fi
            fi
        done
    fi
    
    echo ""
}

# Rust 测试
run_rust_tests() {
    if ! $RUN_RUST; then
        return 0
    fi
    
    echo -e "${CYAN}══════════════════════════════════════════════════════════${NC}"
    echo -e "${CYAN}                  Rust 测试${NC}"
    echo -e "${CYAN}══════════════════════════════════════════════════════════${NC}"
    echo ""
    
    cd "$TESTS_DIR"
    
    # 检查 Cargo.toml
    if [ -f "Cargo.toml" ]; then
        run_test "Rust 单元测试" "cargo test --lib"
        
        if [ -d "tests" ]; then
            run_test "Rust 集成测试" "cargo test --test '*''"
        fi
        
        run_test "Rust 文档测试" "cargo test --doc"
    elif [ -f "rust_tests.rs" ]; then
        # 如果没有 Cargo.toml，尝试直接编译测试
        echo -e "${YELLOW}⚠️  未找到 Cargo.toml，尝试直接编译测试文件${NC}"
        echo ""
        
        if command -v rustc &> /dev/null; then
            run_test "Rust 测试编译" "rustc --test rust_tests.rs -o rust_test_runner && ./rust_test_runner"
        fi
    else
        echo -e "${YELLOW}⚠️  rust_tests.rs 不存在${NC}"
    fi
    
    # 验证示例文件
    local rust_examples_dir="$PROJECT_ROOT/docs/Refactor/examples/rust"
    if [ -d "$rust_examples_dir" ]; then
        echo ""
        echo -e "${BLUE}验证 Rust 示例文件...${NC}"
        
        for file in "$rust_examples_dir"/*.rs; do
            if [ -f "$file" ]; then
                local basename=$(basename "$file")
                echo -n "  检查 $basename... "
                
                if rustc --edition 2021 -Z parse-only "$file" 2>/dev/null; then
                    echo -e "${GREEN}✓${NC}"
                else
                    echo -e "${YELLOW}⚠${NC}"
                fi
            fi
        done
    fi
    
    echo ""
}

# Markdown 验证
run_md_validation() {
    if ! $RUN_MD; then
        return 0
    fi
    
    echo -e "${CYAN}══════════════════════════════════════════════════════════${NC}"
    echo -e "${CYAN}                  Markdown 验证${NC}"
    echo -e "${CYAN}══════════════════════════════════════════════════════════${NC}"
    echo ""
    
    cd "$TESTS_DIR"
    
    if [ -f "validate_md.py" ]; then
        run_test "Markdown 格式验证" "python3 validate_md.py --path '$PROJECT_ROOT/docs'"
    else
        echo -e "${YELLOW}⚠️  validate_md.py 不存在${NC}"
    fi
    
    echo ""
}

# 生成覆盖率报告
generate_coverage() {
    if ! $GENERATE_COVERAGE; then
        return 0
    fi
    
    echo -e "${CYAN}══════════════════════════════════════════════════════════${NC}"
    echo -e "${CYAN}                  覆盖率报告${NC}"
    echo -e "${CYAN}══════════════════════════════════════════════════════════${NC}"
    echo ""
    
    cd "$TESTS_DIR"
    
    if [ -f "coverage_report.py" ]; then
        local output_dir="$TESTS_DIR/coverage_output"
        mkdir -p "$output_dir"
        
        run_test "生成覆盖率报告" "python3 coverage_report.py --output '$output_dir'"
        
        if [ -f "$output_dir/index.html" ]; then
            echo ""
            echo -e "${GREEN}📊 覆盖率报告: file://$output_dir/index.html${NC}"
        fi
    else
        echo -e "${YELLOW}⚠️  coverage_report.py 不存在${NC}"
    fi
    
    echo ""
}

# 生成综合报告
generate_summary() {
    echo ""
    echo -e "${CYAN}╔══════════════════════════════════════════════════════════╗${NC}"
    echo -e "${CYAN}║                  测试结果汇总                            ║${NC}"
    echo -e "${CYAN}╚══════════════════════════════════════════════════════════╝${NC}"
    echo ""
    
    # 测试结果
    echo -e "${BLUE}测试详情:${NC}"
    for result in "${TEST_RESULTS[@]}"; do
        echo "  $result"
    done
    echo ""
    
    # 统计
    local total=$((TESTS_PASSED + TESTS_FAILED))
    local pass_rate=0
    if [ $total -gt 0 ]; then
        pass_rate=$((TESTS_PASSED * 100 / total))
    fi
    
    echo -e "${BLUE}统计信息:${NC}"
    echo -e "  ${GREEN}✅ 通过: $TESTS_PASSED${NC}"
    echo -e "  ${RED}❌ 失败: $TESTS_FAILED${NC}"
    echo -e "  📊 总计: $total"
    echo -e "  📈 通过率: $pass_rate%"
    echo ""
    
    # 最终结果
    if [ $TESTS_FAILED -eq 0 ]; then
        echo -e "${GREEN}╔══════════════════════════════════════════════════════════╗${NC}"
        echo -e "${GREEN}║              🎉 所有测试通过!                            ║${NC}"
        echo -e "${GREEN}╚══════════════════════════════════════════════════════════╝${NC}"
        return 0
    else
        echo -e "${RED}╔══════════════════════════════════════════════════════════╗${NC}"
        echo -e "${RED}║              ⚠️  部分测试失败                            ║${NC}"
        echo -e "${RED}╚══════════════════════════════════════════════════════════╝${NC}"
        return 1
    fi
}

# 主函数
main() {
    print_header
    check_dependencies
    
    # 记录开始时间
    local start_time=$(date +%s)
    
    # 运行测试
    run_lean_tests
    run_rust_tests
    run_md_validation
    generate_coverage
    
    # 记录结束时间
    local end_time=$(date +%s)
    local duration=$((end_time - start_time))
    
    # 生成报告
    generate_summary
    local exit_code=$?
    
    echo ""
    echo -e "${BLUE}⏱️  耗时: ${duration}秒${NC}"
    echo ""
    
    exit $exit_code
}

# 运行主函数
main
