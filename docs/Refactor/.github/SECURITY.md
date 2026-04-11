# 安全政策

## 报告安全漏洞

FormalScience 项目非常重视安全问题。如果您发现了安全漏洞，请通过以下方式负责任地报告。

### 报告方式

**首选方式**（敏感漏洞）：

- 📧 邮箱: **security@formalscience.org**
- 🔐 [GitHub 安全公告](https://github.com/formalscience/formalscience/security/advisories)

**一般安全问题**：

- 🐛 创建公开 Issue（仅用于非敏感问题）
- 💬 加入 [Discord 安全频道](https://discord.gg/formalscience-security)

### 报告内容

请尽可能包含以下信息：

1. **漏洞描述**: 清晰简洁的描述
2. **复现步骤**: 详细的复现说明
3. **影响范围**: 受影响版本和潜在影响
4. **修复建议**: 如果可能，请提供修复建议

### 响应时间

| 阶段 | 时间承诺 |
|------|----------|
| 确认收到 | 48 小时内 |
| 初步评估 | 7 天内 |
| 修复严重漏洞 | 14 天内 |
| 公开披露 | 修复后协调进行 |

## 支持版本

| 版本 | 支持状态 |
|------|----------|
| 2.x | ✅ 完全支持 |
| 1.x | ⚠️ 仅关键安全修复 |
| < 1.0 | ❌ 不再支持 |

## 安全更新

- 📢 订阅 [Release 通知](https://github.com/formalscience/formalscience/releases)
- 📰 关注 [安全公告](https://github.com/formalscience/formalscience/security/advisories)
- 📬 加入 [安全邮件列表](mailto:security-announce@formalscience.org)

## 安全最佳实践

### 用户

```bash
# 保持更新
pip install --upgrade formalscience

# 检查依赖漏洞
pip install safety && safety check
```

### 贡献者

- 遵循 [安全编码指南](../docs/SECURITY.md#安全最佳实践)
- 提交前运行安全扫描
- 不在代码中提交密钥或密码

## 安全功能

- ✅ 自动输入验证
- ✅ 审计日志记录
- ✅ 基于角色的访问控制
- ✅ 敏感数据加密
- ✅ 速率限制

## 致谢

感谢所有负责任地报告安全问题的研究人员：

- [安全贡献者列表](../CONTRIBUTORS.md#security-researchers)

## 联系信息

- 📧 security@formalscience.org
- 🔑 [GPG 公钥](https://formalscience.org/security.gpg)
- 🚨 24/7 应急响应: +1-XXX-XXX-XXXX

---

_完整安全政策请参见 [SECURITY.md](../SECURITY.md)_
