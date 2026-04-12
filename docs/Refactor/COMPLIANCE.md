# 合规说明 (Compliance)

## 概述

本文档详细说明 FormalScience 项目的合规状态，包括许可证合规、第三方依赖管理和法律声明。

## 许可证合规

### 项目许可证

FormalScience 采用以下许可证：

| 组件 | 许可证 | 说明 |
|------|--------|------|
| 核心代码 | MIT | 允许自由使用、修改和分发 |
| 文档 | CC BY-SA 4.0 | 知识共享署名-相同方式共享 |
| 示例代码 | MIT | 与核心代码相同 |

#### MIT 许可证全文

```
MIT License

Copyright (c) 2026 FormalScience Contributors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
```

### 许可证兼容性

```
项目许可证兼容性矩阵

MIT ─────┬───── Apache 2.0 ✓
         ├───── BSD 2/3-Clause ✓
         ├───── MIT ✓
         ├───── ISC ✓
         ├───── Python-2.0 ✓
         └───── LGPL-3.0 ✓ (仅作为库使用)
```

### 文件头模板

#### 源代码文件头

```python
# Copyright (c) 2026 FormalScience Contributors
# SPDX-License-Identifier: MIT
#
# This file is part of FormalScience.
# See LICENSE file for full license text.
```

#### 文档文件头

```markdown
---
copyright: "2026 FormalScience Contributors"
license: "CC BY-SA 4.0"
---
```

## 第三方依赖

### 依赖管理策略

我们遵循以下原则管理第三方依赖：

1. **最小依赖**: 仅使用必要的依赖
2. **活跃维护**: 优先选择活跃维护的项目
3. **许可证审核**: 所有依赖必须通过许可证审核
4. **安全扫描**: 定期扫描依赖的安全漏洞
5. **版本锁定**: 使用锁定文件确保可复现构建

### 核心依赖列表

| 依赖 | 版本 | 许可证 | 用途 |
|------|------|--------|------|
| Python | >=3.9 | PSF | 运行时 |
| NumPy | ^1.24 | BSD | 数值计算 |
| Pandas | ^2.0 | BSD | 数据处理 |
| SymPy | ^1.12 | BSD | 符号计算 |
| NetworkX | ^3.0 | BSD | 图算法 |

### 开发依赖

| 依赖 | 版本 | 许可证 | 用途 |
|------|------|--------|------|
| pytest | ^7.0 | MIT | 测试框架 |
| black | ^23.0 | MIT | 代码格式化 |
| mypy | ^1.0 | MIT | 类型检查 |
| flake8 | ^6.0 | MIT | 代码风格检查 |
| sphinx | ^7.0 | BSD | 文档生成 |

### 许可证兼容性检查

```bash
# 检查依赖许可证
pip install pip-licenses
pip-licenses --format=markdown

# 检查不兼容的许可证
pip-licenses --fail-on="GPL;LGPL;AGPL"
```

### 依赖审计流程

```
添加新依赖
    │
    ▼
┌─────────────┐
│ 许可证审核   │ ──▶ 检查许可证兼容性
└──────┬──────┘
       │
       ▼
┌─────────────┐
│ 安全扫描     │ ──▶ 检查已知漏洞
└──────┬──────┘
       │
       ▼
┌─────────────┐
│ 维护状态检查 │ ──▶ 检查项目活跃度
└──────┬──────┘
       │
       ▼
┌─────────────┐
│ 代码审查     │ ──▶ 审查依赖质量
└──────┬──────┘
       │
       ▼
    批准/拒绝
```

### 禁止的许可证

以下许可证的软件**不得**作为依赖引入：

| 许可证 | 原因 |
|--------|------|
| GPL-2.0/3.0 | 强 copyleft，与 MIT 不兼容（除非作为独立进程） |
| AGPL-3.0 | 强 copyleft，网络使用触发条款 |
| SSPL | 不被 OSI 认可为开源许可证 |
| 专有许可证 | 与开源承诺冲突 |

### 例外情况

在以下情况下，经核心团队批准后可引入严格许可证的依赖：

1. **系统依赖**: 操作系统级别的库
2. **可选功能**: 用户可选择不使用的功能
3. **独立进程**: 通过 IPC 通信的独立进程

## 法律声明

### 免责声明

#### 软件免责声明

```
本软件按"原样"提供，不提供任何形式的明示或暗示担保，包括但不限于
对适销性、特定用途适用性和非侵权性的担保。在任何情况下，作者或版权
持有人均不对任何索赔、损害或其他责任负责，无论是在合同诉讼、侵权诉
讼或其他诉讼中，还是因软件或软件的使用或其他交易而产生或与之相关的。
```

#### 文档免责声明

```
本文档按"原样"提供，仅供信息参考。作者不对文档内容的准确性、完整性
或可靠性做出任何明示或暗示的陈述或保证。使用本文档中的信息所造成的
任何风险由使用者自行承担。
```

### 知识产权

#### 商标

- "FormalScience" 是项目的商标
- 其他商标归其各自所有者所有
- 使用商标需遵守 [商标指南](LICENSE.md)

#### 专利

- 本项目不主张任何专利权
- 贡献者授予用户专利许可（参见 MIT 许可证）

#### 版权归属

```
Copyright (c) 2026 FormalScience Contributors

所有贡献的版权归 respective contributors 所有。
详见 CONTRIBUTORS.md 和 Git 提交历史。
```

### 出口管制

#### 美国出口管制合规

本项目遵守美国出口管制法规：

1. **EAR 分类**: 本项目属于 ECCN 5D002 分类（加密软件）
2. **许可例外**: 符合 TSU 例外（技术和软件不受限制）
3. **禁运国家**: 不向禁运国家出口

#### 最终用户限制

用户不得将本软件用于：

- 开发大规模杀伤性武器
- 侵犯人权的行为
- 违反国际法的行为

### 数据保护合规

#### GDPR 合规

- 详见 [PRIVACY.md](PRIVACY.md)
- 数据处理活动登记
- 数据保护影响评估（DPIA）

#### CCPA 合规

- 加州居民隐私权利
- 数据销售披露：我们不销售个人数据

### 行业特定合规

#### 金融服务业

本项目**不**适合用于：

- 受监管的金融服务
- 关键金融基础设施
- 支付处理系统

#### 医疗保健业

本项目**未**获得以下认证：

- HIPAA 合规
- FDA 认证
- CE 标志（医疗器械）

#### 政府使用

- 美国政府使用权利：根据 FAR 52.227-19
- 受限权利声明适用

## 合规报告

### 合规检查清单

#### 发布前检查

```markdown
## 发布合规检查清单

### 许可证合规
- [ ] 所有源代码文件包含许可证头
- [ ] LICENSE 文件存在于根目录
- [ ] 第三方依赖许可证已审核
- [ ] NOTICE 文件包含所有必需的归属

### 安全合规
- [ ] 安全漏洞扫描通过
- [ ] 依赖项无已知高危漏洞
- [ ] 安全配置已审查

### 隐私合规
- [ ] 隐私政策已更新
- [ ] 数据处理活动已记录
- [ ] Cookie 同意机制正常工作

### 文档合规
- [ ] 免责声明已包含
- [ ] 商标使用已审查
- [ ] 出口管制声明已包含
```

### 合规审计

#### 年度审计

每年进行一次全面合规审计，包括：

1. 许可证合规审查
2. 依赖项安全审计
3. 隐私实践审查
4. 文档准确性检查

#### 持续监控

- 依赖项漏洞监控（Snyk、Dependabot）
- 许可证变更监控
- 合规政策更新监控

### 合规团队

| 角色 | 职责 | 联系方式 |
|------|------|----------|
| 合规负责人 | 总体合规策略 | compliance@formalscience.org |
| 法律顾问 | 法律审查 | legal@formalscience.org |
| 安全官 | 安全合规 | security@formalscience.org |
| DPO | 隐私合规 | dpo@formalscience.org |

## 报告合规问题

如果您发现任何合规问题，请通过以下方式报告：

- **邮箱**: compliance@formalscience.org
- **GitHub**: 创建标记为 `compliance` 的 Issue
- **匿名**: [合规报告表单](https://formalscience.org/compliance-report)

## 更新历史

| 日期 | 版本 | 变更 |
|------|------|------|
| 2026-04-11 | 1.0 | 初始版本发布 |

## 相关文档

- [LICENSE](../LICENSE)
- [CONTRIBUTING.md](CONTRIBUTING.md)
- [SECURITY.md](SECURITY.md)
- [PRIVACY.md](PRIVACY.md)

---

_FormalScience 项目致力于最高的合规标准。_

_最后更新: 2026-04-11_
_版本: 1.0_
