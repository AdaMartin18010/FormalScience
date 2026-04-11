#!/bin/bash
# =============================================================================
# Docker Entrypoint Script - FormalScience Project
# =============================================================================
# 功能：容器启动时的初始化脚本
# =============================================================================

set -e

# 颜色定义
RED='\033[0;31m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
NC='\033[0m'

echo -e "${BLUE}[Entrypoint]${NC} 初始化 FormalScience 容器..."

# -----------------------------------------------------------------------------
# 初始化 Lean 环境
# -----------------------------------------------------------------------------
init_lean() {
    if [ -f "/workspace/lakefile.lean" ]; then
        echo -e "${BLUE}[Entrypoint]${NC} 初始化 Lean 环境..."
        
        # 设置 elan 环境
        if [ -f "$HOME/.elan/env" ]; then
            source "$HOME/.elan/env"
        fi
        
        # 检查是否需要更新依赖
        if [ -d "/workspace/.lake" ]; then
            echo -e "${GREEN}[Entrypoint]${NC} Lean 依赖已存在"
        else
            echo -e "${BLUE}[Entrypoint]${NC} 安装 Lean 依赖..."
            cd /workspace && lake update || true
        fi
    fi
}

# -----------------------------------------------------------------------------
# 初始化 Rust 环境
# -----------------------------------------------------------------------------
init_rust() {
    if [ -f "/workspace/Cargo.toml" ]; then
        echo -e "${BLUE}[Entrypoint]${NC} 初始化 Rust 环境..."
        
        # 设置 cargo 环境
        if [ -f "$HOME/.cargo/env" ]; then
            source "$HOME/.cargo/env"
        fi
        
        # 检查是否需要构建
        if [ ! -d "/workspace/target" ]; then
            echo -e "${BLUE}[Entrypoint]${NC} 构建 Rust 项目..."
            cd /workspace && cargo build 2>/dev/null || true
        fi
    fi
}

# -----------------------------------------------------------------------------
# 初始化 Python 环境
# -----------------------------------------------------------------------------
init_python() {
    if [ -f "/workspace/requirements.txt" ] || [ -f "/workspace/pyproject.toml" ]; then
        echo -e "${BLUE}[Entrypoint]${NC} 初始化 Python 环境..."
        
        # 创建虚拟环境（如果不存在）
        if [ ! -d "/workspace/.venv" ]; then
            echo -e "${BLUE}[Entrypoint]${NC} 创建 Python 虚拟环境..."
            cd /workspace && python3 -m venv .venv
        fi
        
        # 激活虚拟环境
        source /workspace/.venv/bin/activate
        
        # 安装依赖
        if [ -f "/workspace/requirements.txt" ]; then
            pip install -q -r /workspace/requirements.txt 2>/dev/null || true
        fi
    fi
}

# -----------------------------------------------------------------------------
# 设置环境变量
# -----------------------------------------------------------------------------
setup_environment() {
    # 确保所有环境变量可用
    {
        echo "export PATH=\"$HOME/.elan/bin:$HOME/.cargo/bin:$PATH\""
        echo "export ELAN_HOME=\"$HOME/.elan\""
        echo "export RUSTUP_HOME=\"$HOME/.rustup\""
        echo "export CARGO_HOME=\"$HOME/.cargo\""
        echo "export PYTHONPATH=\"/workspace\""
    } >> "$HOME/.bashrc"
}

# -----------------------------------------------------------------------------
# 主函数
# -----------------------------------------------------------------------------
main() {
    # 执行初始化
    init_lean
    init_rust
    init_python
    setup_environment
    
    echo -e "${GREEN}[Entrypoint]${NC} 初始化完成!"
    echo ""
    
    # 显示环境信息
    echo "=================================="
    echo "  FormalScience 开发环境"
    echo "=================================="
    echo ""
    
    # Lean 版本
    if command -v lean &> /dev/null; then
        echo "Lean:    $(lean --version 2>/dev/null || echo 'N/A')"
    fi
    
    # Rust 版本
    if command -v rustc &> /dev/null; then
        echo "Rust:    $(rustc --version 2>/dev/null || echo 'N/A')"
        echo "Cargo:   $(cargo --version 2>/dev/null || echo 'N/A')"
    fi
    
    # Python 版本
    if command -v python3 &> /dev/null; then
        echo "Python:  $(python3 --version 2>/dev/null || echo 'N/A')"
    fi
    
    echo ""
    echo "工作目录: /workspace"
    echo "=================================="
    echo ""
    
    # 执行传入的命令
    exec "$@"
}

main "$@"
