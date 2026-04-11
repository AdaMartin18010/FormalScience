# =============================================================================
# FormalScience - Multi-Language Development Environment
# =============================================================================
# 基于Ubuntu 24.04 LTS，集成Lean 4、Rust和Python环境
# 适用于形式科学验证、程序证明和学术研究
# =============================================================================

FROM ubuntu:24.04

# -----------------------------------------------------------------------------
# 基础环境配置
# -----------------------------------------------------------------------------
ENV DEBIAN_FRONTEND=noninteractive
ENV LANG=C.UTF-8
ENV LC_ALL=C.UTF-8
ENV TZ=Asia/Shanghai

# 工作目录
WORKDIR /workspace

# -----------------------------------------------------------------------------
# 安装系统依赖
# -----------------------------------------------------------------------------
RUN apt-get update && apt-get install -y --no-install-recommends \
    # 基础工具
    curl \
    wget \
    git \
    ca-certificates \
    gnupg \
    lsb-release \
    software-properties-common \
    # 构建工具
    build-essential \
    cmake \
    ninja-build \
    pkg-config \
    # 开发工具
    vim \
    nano \
    less \
    tree \
    htop \
    # 网络工具
    net-tools \
    iputils-ping \
    # Python依赖
    python3 \
    python3-pip \
    python3-venv \
    python3-dev \
    # 其他依赖
    libssl-dev \
    zlib1g-dev \
    libbz2-dev \
    libreadline-dev \
    libsqlite3-dev \
    libncursesw5-dev \
    xz-utils \
    tk-dev \
    libxml2-dev \
    libxmlsec1-dev \
    libffi-dev \
    liblzma-dev \
    # 清理
    && apt-get clean \
    && rm -rf /var/lib/apt/lists/*

# -----------------------------------------------------------------------------
# 安装 Lean 4 (elan + lake)
# -----------------------------------------------------------------------------
ENV ELAN_HOME=/root/.elan
ENV PATH="${ELAN_HOME}/bin:${PATH}"

RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y \
    && . $ELAN_HOME/env \
    && elan default stable \
    && elan toolchain install nightly \
    && elan component add leanprover/lean4:nightly

# 设置lake环境
ENV LAKE_HOME=/root/.lake
ENV PATH="${PATH}:${LAKE_HOME}/bin"

# -----------------------------------------------------------------------------
# 安装 Rust (rustup)
# -----------------------------------------------------------------------------
ENV RUSTUP_HOME=/root/.rustup
ENV CARGO_HOME=/root/.cargo
ENV PATH="${CARGO_HOME}/bin:${PATH}"

RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y \
    --default-toolchain stable \
    --profile default \
    --component rust-src rust-docs rustfmt clippy

# 安装常用Rust工具
RUN . $CARGO_HOME/env \
    && cargo install cargo-watch cargo-edit cargo-tree cargo-audit

# -----------------------------------------------------------------------------
# 配置 Python 环境
# -----------------------------------------------------------------------------
# 升级pip并安装常用科学计算包
RUN python3 -m pip install --no-cache-dir --upgrade pip setuptools wheel \
    && python3 -m pip install --no-cache-dir \
    numpy \
    scipy \
    matplotlib \
    pandas \
    sympy \
    jupyter \
    ipython \
    pytest \
    black \
    flake8 \
    mypy \
    sphinx

# -----------------------------------------------------------------------------
# 复制项目文件
# -----------------------------------------------------------------------------
# 先复制依赖文件（利用Docker缓存层）
COPY pyproject.toml poetry.lock* requirements*.txt ./ 2>/dev/null || true
COPY lakefile.lean manifest.json* ./ 2>/dev/null || true
COPY Cargo.toml Cargo.lock ./ 2>/dev/null || true

# 安装Python项目依赖（如果有）
RUN if [ -f requirements.txt ]; then pip install --no-cache-dir -r requirements.txt; fi

# 复制整个项目
COPY . .

# -----------------------------------------------------------------------------
# 设置环境变量和权限
# -----------------------------------------------------------------------------
# 确保脚本可执行
RUN find . -type f -name "*.sh" -exec chmod +x {} \; 2>/dev/null || true

# 设置默认shell为bash
SHELL ["/bin/bash", "-c"]

# -----------------------------------------------------------------------------
# 健康检查
# -----------------------------------------------------------------------------
HEALTHCHECK --interval=30s --timeout=10s --start-period=5s --retries=3 \
    CMD lean --version && rustc --version && python3 --version || exit 1

# -----------------------------------------------------------------------------
# 启动配置
# -----------------------------------------------------------------------------
EXPOSE 8080 8888

# 入口脚本
COPY scripts/docker_entrypoint.sh /usr/local/bin/entrypoint.sh 2>/dev/null || echo '#!/bin/bash\nexec "$@"' > /usr/local/bin/entrypoint.sh
RUN chmod +x /usr/local/bin/entrypoint.sh

ENTRYPOINT ["/usr/local/bin/entrypoint.sh"]
CMD ["/bin/bash"]

# -----------------------------------------------------------------------------
# 镜像元数据
# -----------------------------------------------------------------------------
LABEL maintainer="FormalScience Team" \
      description="FormalScience development environment with Lean 4, Rust, and Python" \
      version="1.0.0" \
      lean.version="4.x" \
      rust.version="stable" \
      python.version="3.12"
