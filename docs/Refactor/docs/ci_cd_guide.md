# CI/CD 使用指南

---

📌 **内容摘要**

本文档深入探讨CI/CD 使用指南的核心原理和关键方法。内容涵盖其他领域的主要知识点，包括工作流, BPMN, 编排等关键主题。适合有一定基础的学习者系统学习。

**关键词**: 工作流, BPMN, 其他, 编排

📚 **学习目标**
- 掌握CI/CD 使用指南的核心概念和主要方法
- 理解相关理论的应用场景
- 建立该领域的系统性知识框架

🎯 **难度级别**: 中级

⏱️ **预计阅读时间**: 15分钟

**前置知识**: 相关领域的基础概念

---




本指南详细介绍 FormalScience 项目的 CI/CD 工作流配置和使用方法。

---

## 📋 目录

- [CI/CD 使用指南](#cicd-使用指南)
  - [📋 目录](#-目录)
  - [概览](#概览)
  - [工作流说明](#工作流说明)
    - [1. CI 工作流 (ci.yml)](#1-ci-工作流-ciyml)
      - [功能](#功能)
      - [任务依赖关系](#任务依赖关系)
      - [使用方法](#使用方法)
    - [2. 部署工作流 (deploy.yml)](#2-部署工作流-deployyml)
      - [支持的部署目标](#支持的部署目标)
      - [部署流程](#部署流程)
      - [手动触发参数](#手动触发参数)
      - [使用方法](#使用方法-1)
    - [3. 发布工作流 (release.yml)](#3-发布工作流-releaseyml)
      - [功能](#功能-1)
      - [发布流程](#发布流程)
      - [触发方式](#触发方式)
      - [参数说明](#参数说明)
  - [状态徽章](#状态徽章)
  - [配置说明](#配置说明)
    - [必需的秘密变量 (Secrets)](#必需的秘密变量-secrets)
    - [环境变量配置](#环境变量配置)
  - [故障排除](#故障排除)
    - [常见问题](#常见问题)
      - [1. CI 检查失败](#1-ci-检查失败)
      - [2. 部署失败](#2-部署失败)
      - [3. 发布失败](#3-发布失败)
      - [4. 权限问题](#4-权限问题)
  - [最佳实践](#最佳实践)
    - [1. 提交规范](#1-提交规范)
    - [2. 版本管理](#2-版本管理)
    - [3. 分支策略](#3-分支策略)
    - [4. 监控和告警](#4-监控和告警)
  - [参考资源](#参考资源)
  - [更新日志](#更新日志)

---

## 概览

本项目使用 GitHub Actions 实现持续集成和持续部署（CI/CD），包含以下核心工作流：

| 工作流 | 文件 | 用途 | 触发条件 |
|--------|------|------|----------|
| **CI** | `.github/workflows/ci.yml` | 持续集成 | PR、Push、手动触发 |
| **Deploy** | `.github/workflows/deploy.yml` | 部署 | Push到main、标签推送 |
| **Release** | `.github/workflows/release.yml` | 发布 | 版本标签、手动触发 |

---

## 工作流说明

### 1. CI 工作流 (ci.yml)

#### 功能

- **Markdown 检查**: 使用 `markdownlint` 检查文档格式
- **链接检查**: 使用 `lychee` 验证外部链接有效性
- **Lean 4 验证**: 编译和验证 Lean 代码
- **Rust 测试**: 运行 Rust 单元测试、代码格式化检查、Clippy 分析
- **Python 测试**: 运行 Python 测试、代码格式化检查、类型检查
- **安全扫描**: 使用 Trivy 和 CodeQL 进行安全分析
- **生成报告**: 汇总所有检查结果

#### 任务依赖关系

```
markdown-lint ──┐
link-check ─────┤
lean-check ─────┼──► generate-report
rust-test ──────┤
python-test ────┘
security-scan (并行)
```

#### 使用方法

```bash
# 手动触发
gh workflow run ci.yml

# 查看运行状态
gh run list --workflow=ci.yml
```

---

### 2. 部署工作流 (deploy.yml)

#### 支持的部署目标

| 平台 | 说明 | 环境 |
|------|------|------|
| **GitHub Pages** | 静态网站托管 | github-pages |
| **Azure Static Web Apps** | Azure 静态网站 | production/staging |
| **Vercel** | 边缘部署 | production/preview |
| **Netlify** | 静态网站托管 | production/staging |

#### 部署流程

```
build-website ──► deploy-github-pages
              ├──► deploy-azure-static (main分支)
              ├──► deploy-vercel (main分支)
              ├──► deploy-netlify (main分支)
              └──► deploy-rust-docs (main分支)
```

#### 手动触发参数

- `environment`: 选择部署环境（staging/production）
- `dry_run`: 仅预览部署，不实际执行

#### 使用方法

```bash
# 手动触发部署
gh workflow run deploy.yml -f environment=staging

# 部署到生产环境
gh workflow run deploy.yml -f environment=production
```

---

### 3. 发布工作流 (release.yml)

#### 功能

- **自动版本标签**: 根据语义化版本规范创建标签
- **多平台构建**: 为 Linux、Windows、macOS (Intel/ARM) 构建二进制文件
- **Python 包发布**: 构建并发布到 PyPI
- **Rust crates 发布**: 发布到 crates.io
- **自动生成 Changelog**: 基于提交历史生成更新日志
- **GitHub Release**: 创建带附件的发布页面

#### 发布流程

```
create-tag (可选) ──► build-artifacts ──┐
build-python ──────────────────────────┼──► create-release
                                      │
generate-changelog ───────────────────┘
```

#### 触发方式

**方式一：推送标签**

```bash
git tag -a v1.0.0 -m "Release version 1.0.0"
git push origin v1.0.0
```

**方式二：手动触发**

```bash
gh workflow run release.yml -f version=1.0.0 -f draft=false
```

#### 参数说明

- `version`: 发布版本号（如 1.0.0）
- `draft`: 是否为草稿发布
- `prerelease`: 是否为预发布版本

---

## 状态徽章

将以下徽章添加到 `README.md` 中显示构建状态：

```markdown
<!-- CI 状态 -->
![CI](https://github.com/用户名/仓库名/workflows/CI/badge.svg)

<!-- 部署状态 -->
![Deploy](https://github.com/用户名/仓库名/workflows/Deploy/badge.svg)

<!-- 发布状态 -->
![Release](https://github.com/用户名/仓库名/workflows/Release/badge.svg)

<!-- 代码覆盖率 -->
![Coverage](https://img.shields.io/codecov/c/github/用户名/仓库名)

<!-- 最新版本 -->
![Version](https://img.shields.io/github/v/release/用户名/仓库名)

<!-- 许可证 -->
![License](https://img.shields.io/github/license/用户名/仓库名)
```

---

## 配置说明

### 必需的秘密变量 (Secrets)

在 GitHub 仓库设置中配置以下秘密：

| 秘密名称 | 用途 | 必需工作流 |
|----------|------|-----------|
| `AZURE_STATIC_WEB_APPS_API_TOKEN` | Azure 部署令牌 | Deploy |
| `VERCEL_TOKEN` | Vercel 部署令牌 | Deploy |
| `NETLIFY_AUTH_TOKEN` | Netlify 认证令牌 | Deploy |
| `NETLIFY_SITE_ID` | Netlify 站点 ID | Deploy |
| `CARGO_REGISTRY_TOKEN` | crates.io 发布令牌 | Release |
| `SLACK_WEBHOOK_URL` | Slack 通知 | Deploy |

### 环境变量配置

在工作流文件顶部修改以下配置：

```yaml
env:
  CARGO_TERM_COLOR: always    # Rust 输出颜色
  RUST_BACKTRACE: 1           # Rust 错误追踪
  PYTHON_VERSION: '3.11'      # Python 版本
  LEAN_VERSION: '4.8.0'       # Lean 版本
  NODE_VERSION: '20'          # Node.js 版本
```

---

## 故障排除

### 常见问题

#### 1. CI 检查失败

**Markdown Lint 失败**

```bash
# 本地修复
npm install -g markdownlint-cli
markdownlint '**/*.md' --fix
```

**Rust 测试失败**

```bash
# 本地运行测试
cargo test --all-features
cargo fmt --all -- --check
cargo clippy --all-targets --all-features
```

**Python 测试失败**

```bash
# 本地运行测试
pip install pytest black flake8 mypy
pytest -v
black --check .
flake8 .
```

#### 2. 部署失败

**GitHub Pages 部署失败**

- 检查仓库设置中是否启用了 Pages
- 确认 Actions 有写入权限 (`Settings > Actions > General`)

**Azure 部署失败**

- 验证 `AZURE_STATIC_WEB_APPS_API_TOKEN` 是否正确
- 检查 Azure 静态网站应用是否已创建

#### 3. 发布失败

**标签已存在**

```bash
# 删除本地和远程标签
git tag -d v1.0.0
git push --delete origin v1.0.0

# 重新创建
git tag -a v1.0.0 -m "Release version 1.0.0"
git push origin v1.0.0
```

**PyPI 发布失败**

- 确认 `PYPI_API_TOKEN` 已配置
- 检查版本号是否已存在
- 验证 `pyproject.toml` 配置正确

#### 4. 权限问题

确保工作流文件有正确的权限声明：

```yaml
permissions:
  contents: write      # 用于创建 Release
  pages: write         # 用于 GitHub Pages
  id-token: write      # 用于 OIDC 认证
  packages: write      # 用于发布包
```

---

## 最佳实践

### 1. 提交规范

使用约定式提交格式，便于自动生成 Changelog：

```
feat: 添加新功能
fix: 修复 bug
docs: 文档更新
refactor: 代码重构
test: 测试相关
chore: 构建/工具相关
```

### 2. 版本管理

使用发布脚本管理版本：

```bash
# 补丁版本更新
./scripts/release.sh patch

# 次要版本更新
./scripts/release.sh minor

# 主要版本更新
./scripts/release.sh major

# 指定版本号
./scripts/release.sh --version 2.0.0

# 仅生成 Changelog
./scripts/release.sh --changelog-only

# 预览（不执行）
./scripts/release.sh patch --dry-run
```

### 3. 分支策略

```
main ───────────► 生产分支，自动部署
  │
  ├── develop ───► 开发分支，合并功能
  │     │
  │     ├── feature/xxx ─► 功能分支
  │     └── fix/xxx ─────► 修复分支
  │
  └── release/v1.0.0 ───► 发布分支
```

### 4. 监控和告警

配置 Slack 通知以获取部署状态：

1. 创建 Slack Incoming Webhook
2. 添加到 GitHub Secrets: `SLACK_WEBHOOK_URL`
3. 在需要的工作流中添加通知步骤

---

## 参考资源

- [GitHub Actions 文档](https://docs.github.com/en/actions)
- [GitHub Pages 文档](https://docs.github.com/en/pages)
- [Semantic Versioning](https://semver.org/lang/zh-CN/)
- [约定式提交](https://www.conventionalcommits.org/zh-hans/v1.0.0/)

---

## 更新日志

| 日期 | 版本 | 变更说明 |
|------|------|----------|
| 2024-XX-XX | 1.0.0 | 初始 CI/CD 配置 |
