# Docker 部署配置使用文档

---

📌 **内容摘要**

本文档深入探讨Docker 部署配置使用文档的核心原理和关键方法。内容涵盖其他领域的主要知识点，包括相关理论、方法及应用。适合有一定基础的学习者系统学习。

**关键词**: 其他

📚 **学习目标**
- 掌握Docker 部署配置使用文档的核心概念和主要方法
- 理解相关理论的应用场景
- 建立该领域的系统性知识框架

🎯 **难度级别**: 中级

⏱️ **预计阅读时间**: 15分钟

**前置知识**: 相关领域的基础概念

---




> **FormalScience 项目 - 多语言开发环境**
>
> 支持 Lean 4、Rust、Python 的容器化开发环境

---

## 目录

- [Docker 部署配置使用文档](#docker-部署配置使用文档)
  - [目录](#目录)
  - [快速开始](#快速开始)
  - [安装 Docker](#安装-docker)
    - [Windows](#windows)
    - [macOS](#macos)
    - [Linux (Ubuntu/Debian)](#linux-ubuntudebian)
  - [构建镜像](#构建镜像)
    - [使用构建脚本（推荐）](#使用构建脚本推荐)
    - [使用 Docker 命令](#使用-docker-命令)
  - [运行容器](#运行容器)
    - [使用运行脚本（推荐）](#使用运行脚本推荐)
    - [使用 Docker 命令](#使用-docker-命令-1)
  - [Docker Compose 使用](#docker-compose-使用)
    - [启动服务](#启动服务)
    - [常用命令](#常用命令)
  - [常见命令](#常见命令)
    - [容器管理](#容器管理)
    - [镜像管理](#镜像管理)
    - [进入容器](#进入容器)
    - [文件操作](#文件操作)
    - [网络管理](#网络管理)
    - [卷管理](#卷管理)
  - [故障排除](#故障排除)
    - [常见问题](#常见问题)
      - [1. 端口冲突](#1-端口冲突)
      - [2. 权限问题](#2-权限问题)
      - [3. 镜像构建失败](#3-镜像构建失败)
      - [4. 容器无法启动](#4-容器无法启动)
      - [5. 网络连接问题](#5-网络连接问题)
    - [性能优化](#性能优化)
    - [调试技巧](#调试技巧)
  - [参考资源](#参考资源)

---

## 快速开始

```bash
# 1. 克隆项目
git clone <repository-url>
cd FormalScience

# 2. 构建镜像
./docs/Refactor/scripts/docker_build.sh

# 3. 运行容器
./docs/Refactor/scripts/docker_run.sh

# 或使用 Docker Compose
docker-compose -f docs/Refactor/docker-compose.yml up -d
```

---

## 安装 Docker

### Windows

1. **安装 Docker Desktop**

   ```powershell
   # 下载地址
   https://www.docker.com/products/docker-desktop
   ```

2. **启用 WSL2 后端**（推荐）

   ```powershell
   # PowerShell 管理员权限
   wsl --install
   wsl --set-default-version 2
   ```

3. **验证安装**

   ```powershell
   docker --version
   docker-compose --version
   ```

### macOS

```bash
# 使用 Homebrew 安装
brew install --cask docker

# 启动 Docker Desktop
open /Applications/Docker.app

# 验证
docker --version
```

### Linux (Ubuntu/Debian)

```bash
# 更新包索引
sudo apt-get update

# 安装依赖
sudo apt-get install -y apt-transport-https ca-certificates curl gnupg lsb-release

# 添加 Docker GPG 密钥
curl -fsSL https://download.docker.com/linux/ubuntu/gpg | sudo gpg --dearmor -o /usr/share/keyrings/docker-archive-keyring.gpg

# 添加仓库
echo "deb [arch=amd64 signed-by=/usr/share/keyrings/docker-archive-keyring.gpg] https://download.docker.com/linux/ubuntu $(lsb_release -cs) stable" | sudo tee /etc/apt/sources.list.d/docker.list > /dev/null

# 安装 Docker
sudo apt-get update
sudo apt-get install -y docker-ce docker-ce-cli containerd.io docker-compose-plugin

# 添加用户到 docker 组
sudo usermod -aG docker $USER
newgrp docker

# 验证
docker --version
docker compose version
```

---

## 构建镜像

### 使用构建脚本（推荐）

```bash
# 进入脚本目录
cd docs/Refactor/scripts

# 构建最新版本
./docker_build.sh

# 构建指定版本
./docker_build.sh v1.0.0

# 无缓存构建
./docker_build.sh -n v1.0.0

# 构建并推送到仓库
./docker_build.sh -p v1.0.0

# 多平台构建
./docker_build.sh --platform linux/amd64,linux/arm64 v1.0.0
```

### 使用 Docker 命令

```bash
# 基本构建
docker build -f docs/Refactor/Dockerfile -t formalscience:latest .

# 带构建参数
docker build \
  --build-arg LEAN_VERSION=nightly \
  --build-arg RUST_VERSION=stable \
  -f docs/Refactor/Dockerfile \
  -t formalscience:latest .

# 使用 Buildx 构建
docker buildx build \
  --platform linux/amd64,linux/arm64 \
  -t formalscience:latest \
  -f docs/Refactor/Dockerfile \
  --push .
```

---

## 运行容器

### 使用运行脚本（推荐）

```bash
# 进入脚本目录
cd docs/Refactor/scripts

# 交互式启动（默认）
./docker_run.sh

# 后台运行
./docker_run.sh -d

# 运行后自动删除容器
./docker_run.sh -r "python3 script.py"

# 指定端口
./docker_run.sh -j 8889 -w 8081

# 运行 Jupyter
./docker_run.sh -d "jupyter lab --ip=0.0.0.0 --allow-root"

# 启用 GPU
./docker_run.sh --gpu "python3 train.py"
```

### 使用 Docker 命令

```bash
# 基本运行
docker run -it --name formalscience \
  -v $(pwd):/workspace \
  -p 8888:8888 -p 8080:8080 \
  formalscience:latest

# 后台运行
docker run -d --name formalscience \
  -v $(pwd):/workspace \
  -p 8888:8888 \
  formalscience:latest

# 运行特定命令
docker run --rm formalscience:latest lean --version
docker run --rm formalscience:latest rustc --version
docker run --rm formalscience:latest python3 --version

# 使用 GPU
docker run --gpus all -it formalscience:latest
```

---

## Docker Compose 使用

### 启动服务

```bash
# 开发环境
docker-compose -f docs/Refactor/docker-compose.yml up -d formalscience-dev

# Jupyter 服务
docker-compose -f docs/Refactor/docker-compose.yml --profile jupyter up -d jupyter

# 文档构建
docker-compose -f docs/Refactor/docker-compose.yml --profile docs up docs
```

### 常用命令

```bash
# 启动所有服务
docker-compose up -d

# 查看日志
docker-compose logs -f

# 停止服务
docker-compose down

# 停止并删除卷
docker-compose down -v

# 重启服务
docker-compose restart

# 构建并启动
docker-compose up -d --build

# 执行命令
docker-compose exec formalscience-dev /bin/bash
docker-compose exec formalscience-dev lean --version
```

---

## 常见命令

### 容器管理

```bash
# 列出运行中的容器
docker ps

# 列出所有容器
docker ps -a

# 启动容器
docker start formalscience

# 停止容器
docker stop formalscience

# 重启容器
docker restart formalscience

# 删除容器
docker rm formalscience

# 强制删除
docker rm -f formalscience
```

### 镜像管理

```bash
# 列出镜像
docker images

# 删除镜像
docker rmi formalscience:latest

# 清理未使用的镜像
docker image prune

# 查看镜像历史
docker history formalscience:latest

# 查看镜像详情
docker inspect formalscience:latest
```

### 进入容器

```bash
# 交互式进入
docker exec -it formalscience /bin/bash

# 以 root 身份进入
docker exec -it -u root formalscience /bin/bash

# 查看容器进程
docker top formalscience

# 查看容器资源使用
docker stats formalscience
```

### 文件操作

```bash
# 从容器复制文件到主机
docker cp formalscience:/workspace/file.txt ./

# 从主机复制文件到容器
docker cp ./file.txt formalscience:/workspace/

# 查看容器日志
docker logs formalscience
docker logs -f formalscience  # 实时跟踪
docker logs --tail 100 formalscience  # 最后100行
```

### 网络管理

```bash
# 列出网络
docker network ls

# 查看网络详情
docker network inspect formalscience-network

# 连接容器到网络
docker network connect formalscience-network container_name

# 断开容器网络
docker network disconnect formalscience-network container_name
```

### 卷管理

```bash
# 列出卷
docker volume ls

# 查看卷详情
docker volume inspect formalscience-data

# 清理未使用的卷
docker volume prune

# 备份卷
docker run --rm -v formalscience-data:/data -v $(pwd):/backup alpine tar czf /backup/backup.tar.gz -C /data .

# 恢复卷
docker run --rm -v formalscience-data:/data -v $(pwd):/backup alpine tar xzf /backup/backup.tar.gz -C /data
```

---

## 故障排除

### 常见问题

#### 1. 端口冲突

```bash
# 错误: bind: address already in use
# 解决方案: 更换端口或停止占用端口的进程

# 查找占用端口的进程
lsof -i :8888  # macOS/Linux
netstat -ano | findstr :8888  # Windows

# 使用不同端口启动
./docker_run.sh -j 8889 -w 8081
```

#### 2. 权限问题

```bash
# 错误: permission denied
# 解决方案: 检查文件权限或使用 sudo

# 修复文件权限
sudo chown -R $USER:$USER ./

# 或者使用 sudo 运行 Docker
sudo docker run ...
```

#### 3. 镜像构建失败

```bash
# 清理缓存后重试
./docker_build.sh -n

# 或者手动清理
docker system prune -a
docker buildx prune -f
```

#### 4. 容器无法启动

```bash
# 查看详细日志
docker logs formalscience

# 检查容器状态
docker inspect formalscience

# 以调试模式启动
docker run -it --entrypoint /bin/bash formalscience:latest
```

#### 5. 网络连接问题

```bash
# 检查网络配置
docker network inspect bridge

# 重启 Docker 服务
# Windows/macOS: 重启 Docker Desktop
# Linux:
sudo systemctl restart docker
```

### 性能优化

```bash
# 增加 Docker 内存限制 (Docker Desktop)
# Settings -> Resources -> Memory

# 使用多阶段构建减小镜像大小
# 参考 Dockerfile 中的生产阶段

# 清理未使用的资源
docker system prune -a --volumes
```

### 调试技巧

```bash
# 查看容器详细信息
docker inspect formalscience

# 查看容器进程
docker exec formalscience ps aux

# 查看容器网络配置
docker exec formalscience ip addr

# 实时监控容器资源
docker stats formalscience

# 导出容器文件系统
docker export formalscience -o formalscience.tar
```

---

## 参考资源

- [Docker 官方文档](https://docs.docker.com/)
- [Docker Compose 文档](https://docs.docker.com/compose/)
- [Lean 4 官方文档](https://lean-lang.org/lean4/doc/)
- [Rust Docker 镜像](https://hub.docker.com/_/rust)
- [Python Docker 镜像](https://hub.docker.com/_/python)

---

**最后更新**: 2025年4月

如有问题，请提交 Issue 或联系开发团队。
