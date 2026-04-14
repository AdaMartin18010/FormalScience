# FormalScience RFC标准映射文档集

## 项目概述

本文档集是FormalScience项目的核心组成部分，全面映射了计算机网络领域的14个核心RFC标准。
每个文档均按照统一结构编写，包含协议概述、详细说明、报文格式、状态机、安全性考虑、教材对标、实现示例和现代应用等内容。

---

## 文档清单

### 网络层协议

| 文档 | RFC编号 | 标题 | 行数 | 核心内容 |
|------|---------|------|------|----------|
| [RFC0791-IP协议.md](RFC0791-IP协议.md) | RFC 791 | Internet Protocol | 854 | IPv4协议、报文格式、分片重组、路由 |
| [RFC3168-ECN.md](RFC3168-ECN.md) | RFC 3168 | Explicit Congestion Notification | 867 | ECN机制、拥塞标记、TCP友好性 |

### 传输层协议

| 文档 | RFC编号 | 标题 | 行数 | 核心内容 |
|------|---------|------|------|----------|
| [RFC0793-TCP协议.md](RFC0793-TCP协议.md) | RFC 793 | Transmission Control Protocol | 1046 | TCP连接管理、可靠传输、状态机 |
| [RFC0768-UDP协议.md](RFC0768-UDP协议.md) | RFC 768 | User Datagram Protocol | 843 | 无连接传输、报文格式、应用 |
| [RFC5681-TCP拥塞控制.md](RFC5681-TCP拥塞控制.md) | RFC 5681 | TCP Congestion Control | 765 | 慢启动、拥塞避免、快速恢复 |
| [RFC8312-CUBIC.md](RFC8312-CUBIC.md) | RFC 8312 | CUBIC Congestion Control | 777 | 高速网络拥塞控制、三次方增长 |

### 应用层协议

| 文档 | RFC编号 | 标题 | 行数 | 核心内容 |
|------|---------|------|------|----------|
| [RFC1034-RFC1035-DNS.md](RFC1034-RFC1035-DNS.md) | RFC 1034/1035 | Domain Name System | 886 | DNS架构、报文格式、解析过程 |
| [RFC2616-RFC7230-HTTP.md](RFC2616-RFC7230-HTTP.md) | RFC 2616/7230 | Hypertext Transfer Protocol | 1085 | HTTP/1.1协议、方法、状态码 |
| [RFC7540-HTTP2.md](RFC7540-HTTP2.md) | RFC 7540 | HTTP/2 | 962 | 二进制分帧、多路复用、HPACK |
| [RFC8446-TLS1.3协议.md](RFC8446-TLS1.3协议.md) | RFC 8446 | TLS 1.3 | ~1200 | 1-RTT握手、0-RTT、HKDF密钥派生、AEAD |
| [RFC9000-QUIC.md](RFC9000-QUIC.md) | RFC 9000 | QUIC | 891 | QUIC传输、0-RTT、连接迁移 |
| [RFC9002-TCP性能.md](RFC9002-TCP性能.md) | RFC 9002 | QUIC Loss Detection | 905 | QUIC丢包检测、PTO、拥塞控制 |

### 服务质量（QoS）

| 文档 | RFC编号 | 标题 | 行数 | 核心内容 |
|------|---------|------|------|----------|
| [RFC1633-IntServ.md](RFC1633-IntServ.md) | RFC 1633 | Integrated Services | 795 | IntServ架构、RSVP、资源预留 |
| [RFC2474-DiffServ.md](RFC2474-DiffServ.md) | RFC 2474 | Differentiated Services | 902 | DSCP、PHB、区分服务 |

---

## 文档结构

每个RFC文档包含以下标准章节：

### 1. RFC概述

- 基本信息（编号、标题、日期、状态）
- 历史背景
- 核心贡献

### 2. 协议详细说明

- 设计原则
- 核心机制
- 架构描述

### 3. 报文格式

- 协议数据单元结构
- 字段详解
- 编码规则

### 4. 状态机

- 协议状态转换
- 事件处理逻辑
- 状态图（Mermaid格式）

### 5. 安全性考虑

- 已知安全威胁
- 攻击缓解措施
- 安全最佳实践

### 6. 与教材对标的章节

- 《计算机网络：自顶向下方法》
- 《TCP/IP详解》
- 《计算机网络》（谢希仁）

### 7. 实现示例

- Python协议实现
- C语言关键代码
- 形式化规约（TLA+风格）

### 8. 现代应用

- 部署现状
- 协议演进
- 相关RFC关系

---

## 统计信息

- **总文档数**: 14
- **总行数**: 约12,200行
- **总大小**: 约360KB
- **覆盖协议**: IP、TCP、UDP、DNS、HTTP、HTTP/2、TLS 1.3、QUIC、IntServ、DiffServ、ECN
- **包含算法**: 慢启动、拥塞避免、CUBIC、丢包检测、HKDF密钥派生

---

## 学习路径建议

### 基础阶段

1. RFC0791-IP协议 - 理解网络层基础
2. RFC0768-UDP协议 - 理解无连接传输
3. RFC0793-TCP协议 - 理解面向连接传输

### 应用层阶段

1. RFC1034-RFC1035-DNS - 域名系统
2. RFC2616-RFC7230-HTTP - Web基础

### 进阶阶段

1. RFC5681-TCP拥塞控制 - 经典拥塞控制
2. RFC3168-ECN - 显式拥塞通知
3. RFC7540-HTTP2 - 现代Web协议

### 高级阶段

1. RFC1633-IntServ - 综合服务体系
2. RFC2474-DiffServ - 区分服务体系
3. RFC8312-CUBIC - 高速网络拥塞控制
4. RFC9000-QUIC - 下一代传输协议
5. RFC9002-TCP性能 - QUIC拥塞控制

---

## 实现说明

所有Python实现代码均经过测试，可直接运行。主要包含：

- **协议解析器**: IP、TCP、UDP、DNS报文解析
- **状态机实现**: TCP连接状态机、拥塞控制状态机
- **算法实现**: CUBIC、RED、Token Bucket等
- **完整示例**: HTTP服务器、DNS解析器、QUIC帧处理

---

## 相关资源

### 官方RFC文档

- [IETF RFC Editor](https://www.rfc-editor.org/)
- [RFC 791 - IP](https://tools.ietf.org/html/rfc791)
- [RFC 793 - TCP](https://tools.ietf.org/html/rfc793)

### 推荐教材

- James F. Kurose, Keith W. Ross. "计算机网络：自顶向下方法"
- W. Richard Stevens. "TCP/IP详解"
- 谢希仁. "计算机网络"

### 开源实现

- Linux Kernel: `net/ipv4/` 目录
- Chromium: QUIC实现
- ngtcp2: QUIC库

---

## 维护说明

- **版本**: 1.0
- **创建日期**: 2026年
- **状态**: 核心RFC映射完成
- **维护者**: FormalScience项目团队

---

_本文档集是FormalScience项目的核心知识资产，涵盖了计算机网络协议栈的核心协议和标准。_
