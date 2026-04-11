# 安全政策 (Security Policy)

## 概述

本文档定义了 FormalScience 项目的安全政策，包括支持版本、漏洞报告流程和安全最佳实践。

## 支持版本

以下版本目前正在接收安全更新：

| 版本 | 支持状态 | 说明 |
|------|----------|------|
| 2.x | ✅ 完全支持 | 当前稳定版本，接收所有安全更新 |
| 1.x | ⚠️ 有限支持 | 仅接收关键安全漏洞修复 |
| < 1.0 | ❌ 不再支持 | 建议升级到最新版本 |

## 报告漏洞

### 如何报告安全漏洞

如果您发现了安全漏洞，请按照以下流程报告：

#### 1. 私密报告（推荐）

- **邮箱**: security@formalscience.org
- **主题**: `[SECURITY] 漏洞简要描述`
- **内容要求**:
  - 漏洞的详细描述
  - 复现步骤
  - 影响范围评估
  - 可能的修复建议（可选）

#### 2. GitHub 安全公告

- 访问 [Security Advisories](https://github.com/formalscience/formalscience/security/advisories)
- 点击 "New draft security advisory"
- 按照模板填写漏洞信息

### 报告确认

- 我们会在 **48 小时内** 确认收到您的报告
- 严重漏洞将在 **72 小时内** 启动响应流程
- 报告者将收到漏洞处理进展的定期更新

### 漏洞披露时间线

| 阶段 | 时间 | 说明 |
|------|------|------|
| 确认收到 | 48 小时内 | 确认报告并分配 CVE（如适用） |
| 初步评估 | 7 天内 | 完成漏洞严重性评估 |
| 修复开发 | 根据严重性 | 严重：14天，高：30天，中：60天 |
| 协调披露 | 修复后 | 公开披露漏洞详情和修复方案 |

## 安全更新

### 获取安全更新

- **GitHub Releases**: 订阅 [Release 通知](https://github.com/formalscience/formalscience/releases)
- **安全公告**: 关注 [Security Advisories](https://github.com/formalscience/formalscience/security/advisories)
- **邮件列表**: 订阅 security-announce@formalscience.org

### 安全修复版本号规则

安全修复将使用以下版本号格式：

- 主要版本号不变（如 2.x）
- 次要版本号递增（如 2.1 → 2.2）
- 修订号用于紧急安全补丁（如 2.1.0 → 2.1.1）

### 已知漏洞数据库

我们维护一个公开的已知漏洞数据库：

- [GitHub Security Advisories](https://github.com/formalscience/formalscience/security/advisories)
- [CVE 列表](https://cve.mitre.org/cgi-bin/cvekey.cgi?keyword=formalscience)

## 安全最佳实践

### 对于用户

#### 1. 保持更新

```bash
# 检查当前版本
formalscience --version

# 更新到最新版本
pip install --upgrade formalscience
```

#### 2. 依赖管理

```bash
# 定期检查依赖漏洞
pip install safety
safety check

# 或使用 pip-audit
pip install pip-audit
pip-audit
```

#### 3. 配置安全

```yaml
# config.yaml - 安全配置示例
security:
  # 启用审计日志
  audit_logging: true

  # 设置安全头部
  security_headers:
    x_frame_options: "DENY"
    x_content_type_options: "nosniff"

  # 限制敏感操作
  rate_limiting:
    enabled: true
    max_requests: 100
    window_seconds: 60
```

#### 4. 数据保护

```python
# 敏感数据加密示例
from formalscience.security import encrypt_sensitive_data

# 加密存储敏感配置
encrypted_config = encrypt_sensitive_data(
    data=sensitive_data,
    key_id="your-key-id"
)
```

### 对于贡献者

#### 1. 安全编码指南

- **输入验证**: 始终验证和清理用户输入
- **输出编码**: 防止 XSS 和其他注入攻击
- **身份验证**: 使用强身份验证机制
- **授权**: 实施最小权限原则
- **加密**: 敏感数据必须加密存储和传输

#### 2. 代码审查清单

```markdown
## 安全代码审查清单

- [ ] 是否验证所有用户输入？
- [ ] 是否使用参数化查询防止 SQL 注入？
- [ ] 是否正确处理敏感数据（加密、脱敏）？
- [ ] 是否实施了适当的访问控制？
- [ ] 是否记录安全相关事件？
- [ ] 是否更新依赖到安全版本？
- [ ] 是否移除调试代码和硬编码密钥？
```

#### 3. 依赖安全

```bash
# 提交前检查依赖
pip list --outdated

# 检查已知漏洞
safety check -r requirements.txt

# 更新锁定文件
pip-compile --upgrade requirements.in
```

## 安全功能

### 内置安全机制

| 功能 | 描述 | 版本 |
|------|------|------|
| 输入验证 | 自动验证和清理用户输入 | 2.0+ |
| 审计日志 | 记录安全相关操作 | 2.0+ |
| 访问控制 | 基于角色的权限管理 | 2.1+ |
| 数据加密 | 敏感数据自动加密 | 2.1+ |
| 安全头部 | HTTP 安全头部自动添加 | 2.2+ |

### 配置安全选项

```python
# 启用所有安全功能
from formalscience import configure_security

configure_security(
    input_validation=True,
    audit_logging=True,
    encryption=True,
    rate_limiting=True,
    security_headers=True
)
```

## 合规性

本项目遵循以下安全标准和法规：

- **ISO 27001**: 信息安全管理体系
- **GDPR**: 通用数据保护条例（针对欧盟用户）
- **CCPA**: 加州消费者隐私法案
- **OWASP Top 10**: 防范最常见的 Web 应用安全风险

## 联系信息

- **安全团队**: security@formalscience.org
- **GPG 密钥**: [下载公钥](https://formalscience.org/security.gpg)
- **应急响应**: +1-XXX-XXX-XXXX（24/7）

## 致谢

我们感谢以下安全研究人员对项目安全做出的贡献：

- [安全贡献者列表](CONTRIBUTORS.md#security-researchers)

---

_最后更新: 2026-04-11_
_版本: 1.0_
