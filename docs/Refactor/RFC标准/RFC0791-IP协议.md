# RFC 791 - Internet Protocol (IP)

## 1. RFC概述

### 1.1 基本信息

- **RFC编号**: RFC 791
- **标题**: Internet Protocol
- **发布日期**: 1981年9月
- **状态**: Internet Standard
- **替代**: RFC 760
- **更新**: RFC 1349, RFC 2474, RFC 6864

### 1.2 历史背景

RFC 791定义了互联网协议（IP）的第二个主要版本，通常称为IPv4。它是互联网基础架构的核心协议之一，与TCP协议（RFC 793）共同构成了TCP/IP协议栈的基础。

### 1.3 核心贡献

- 定义了无连接、不可靠的数据报传输服务
- 确立了分层网络架构的原则
- 规定了IP地址结构和路由机制
- 奠定了互联网互联的基础

---

## 2. 协议详细说明

### 2.1 设计原则

#### 2.1.1 无连接服务

IP协议提供无连接的数据报服务，每个数据包独立路由，不保证：

- 数据包按序到达
- 数据包不重复
- 数据包可靠交付

#### 2.1.2 尽力而为交付

IP采用"Best Effort"交付模型：

- 不保证成功交付
- 不保证服务质量
- 发生错误时可能静默丢弃

### 2.2 核心功能

#### 2.2.1 寻址

- **地址长度**: 32位（4字节）
- **表示形式**: 点分十进制（如192.168.1.1）
- **地址空间**: 约43亿个地址

#### 2.2.2 路由

- 基于目的IP地址进行路由决策
- 支持动态路由协议
- 分层次的路由结构

#### 2.2.3 分片与重组

- 允许大数据包分片传输
- 每个分片独立路由
- 目的地重组

---

## 3. 报文格式

### 3.1 IPv4首部格式

```
 0                   1                   2                   3
 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|Version|  IHL  |Type of Service|          Total Length         |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|         Identification        |Flags|      Fragment Offset    |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|  Time to Live |    Protocol   |         Header Checksum       |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                       Source Address                          |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                    Destination Address                        |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                    Options (if IHL > 5)                       |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                    Data (Payload)                             |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
```

### 3.2 首部字段详解

| 字段 | 长度 | 描述 |
|------|------|------|
| Version | 4 bits | IP版本，IPv4为4 |
| IHL | 4 bits | 首部长度，单位为4字节字，最小值为5（20字节） |
| Type of Service | 8 bits | 服务类型，用于QoS |
| Total Length | 16 bits | 总长度（首部+数据），最大65535字节 |
| Identification | 16 bits | 数据包标识，用于分片重组 |
| Flags | 3 bits | 分片标志（保留、DF、MF） |
| Fragment Offset | 13 bits | 分片偏移，单位为8字节 |
| Time to Live | 8 bits | 生存时间，每跳减1，到0丢弃 |
| Protocol | 8 bits | 上层协议类型 |
| Header Checksum | 16 bits | 首部校验和 |
| Source Address | 32 bits | 源IP地址 |
| Destination Address | 32 bits | 目的IP地址 |
| Options | 可变 | 可选字段 |

### 3.3 服务类型字段（ToS）

```
 0   1   2   3   4   5   6   7
+---+---+---+---+---+---+---+---+
|   Precedence    |D|T|R|C|  0  |
+---+---+---+---+---+---+---+---+
```

- **Precedence**: 优先级（0-7）
- **D**: 最小延迟（Delay）
- **T**: 最大吞吐量（Throughput）
- **R**: 最高可靠性（Reliability）
- **C**: 最小成本（Cost）

### 3.4 分片标志

| 位 | 名称 | 含义 |
|----|------|------|
| 0 | 保留 | 必须为0 |
| 1 | DF (Don't Fragment) | 1=禁止分片 |
| 2 | MF (More Fragments) | 1=还有更多分片 |

---

## 4. 状态机

### 4.1 IP层处理状态机

```
                    +------------------+
                    |     START        |
                    +--------+---------+
                             |
                             v
                    +--------+---------+
             +----->|  Receive Packet  |<------+
             |      +--------+---------+       |
             |               |                 |
             |    +----------+----------+      |
             |    |                     |      |
             v    v                     v      |
    +--------+----+----+      +---------+------+-----+
    | Validate Header   |      |  Check Options      |
    +--------+----+----+      +---------+------+-----+
             |                          |           |
             | Valid                    |           |
             v                          v           |
    +--------+---------+      +---------+----------+|
    | Check Destination|      | Process Options    ||
    +--------+---------+      +---------+----------+|
             |                          |           |
             | For this host            v           |
             v                 +--------+---------+ |
    +--------+---------+       | Reconstruct      | |
    |   Local Host?    +------>| Fragmentation?   | |
    +--------+---------+       +--------+---------+ |
             |                          |           |
       No   |                          | Complete  |
             v                          v           |
    +--------+---------+       +--------+---------+ |
    |  Forward Packet  |       | Deliver to Upper | |
    +--------+---------+       | Layer            | |
             |                 +--------+---------+ |
             |                          |           |
             v                          v           |
    +--------+---------+                +----------++
    |  Update TTL      |                           |
    |  Update Checksum |                           |
    +--------+---------+                           |
             |                                     |
             v                                     |
    +--------+---------+                           |
    |   Route Lookup   +---------------------------+
    +------------------+
```

### 4.2 分片处理状态机

```
                    +------------------+
                    |  Receive Packet  |
                    +--------+---------+
                             |
                             v
                    +--------+---------+
                    | Check DF Flag    |
                    +--------+---------+
                             |
              +--------------+--------------+
              |                             |
           DF=1                           DF=0
              |                             |
              v                             v
    +---------+---------+      +------------+----------+
    | MTU < Packet Size?|      | MTU < Packet Size?    |
    +---------+---------+      +------------+----------+
              |                             |
        Yes   |                             |  Yes
              v                             v
    +---------+---------+      +------------+----------+
    | Send ICMP         |      | Calculate Fragments   |
    | Fragmentation     |      | Split Packet          |
    | Needed            |      | Update Headers        |
    | (Type 3, Code 4)  |      | Send Fragments        |
    +---------+---------+      +------------+----------+
              |                             |
              v                             v
    +---------+---------+      +------------+----------+
    |      DROP         |      | Send Complete Packet  |
    +-------------------+      +-----------------------+
```

---

## 5. 安全性考虑

### 5.1 已知安全漏洞

#### 5.1.1 IP欺骗（IP Spoofing）

- **攻击方式**: 伪造源IP地址发送数据包
- **风险**: 绕过基于IP的访问控制，发起DDoS攻击
- **缓解措施**:
  - 入口/出口过滤（RFC 2827）
  - 反向路径转发检查
  - 使用IPsec认证

#### 5.1.2 分片攻击

- **Tiny Fragment Attack**: 利用极小分片绕过防火墙检测
- **Overlapping Fragment Attack**: 利用重叠分片覆盖关键首部字段
- **缓解措施**:
  - 重组后再检查
  - 丢弃重叠分片
  - 最小分片大小检查

#### 5.1.3 ICMP重定向攻击

- **攻击方式**: 发送伪造ICMP重定向消息
- **风险**: 流量劫持
- **缓解措施**: 禁用ICMP重定向处理

### 5.2 IPsec扩展

RFC 791本身不提供安全机制，但定义了扩展机制：

- **认证首部（AH）**: RFC 4302
- **封装安全载荷（ESP）**: RFC 4303
- **Internet密钥交换（IKE）**: RFC 7296

### 5.3 形式化安全分析

```
安全属性：
1. 完整性：IP首部校验和提供基本完整性检查
   ∀p ∈ Packet: checksum(p.header) = p.header.checksum

2. 可用性：TTL机制防止无限循环
   ∀p ∈ Packet: ∀hop ∈ Path(p): p.TTL > 0

3. 无连接匿名性：
   ¬∃state ∈ IP_State: correlates(packets)
```

---

## 6. 与教材对标的章节

### 6.1 《计算机网络：自顶向下方法》

| RFC 791内容 | 对应章节 |
|------------|----------|
| IP协议概述 | 第4章：网络层：数据平面 |
| IPv4编址 | 4.4 IPv4编址 |
| 数据报格式 | 4.4.1 IPv4数据报格式 |
| 分片与重组 | 4.4.2 IPv4分片 |
| NAT | 4.5 网络地址转换（NAT） |

### 6.2 《TCP/IP详解 卷1：协议》

| RFC 791内容 | 对应章节 |
|------------|----------|
| IP首部 | 第3章：IP：网际协议 |
| IP路由 | 第9章：IP选路 |
| 分片 | 第11章：ICMP：Internet控制报文协议 |

### 6.3 《计算机网络》（谢希仁）

| RFC 791内容 | 对应章节 |
|------------|----------|
| IP协议 | 第4章：网络层 - 4.2 网际协议IP |
| IP地址 | 4.2.2 分类的IP地址 |
| 分组转发 | 4.2.6 IP层转发分组的流程 |

---

## 7. 实现示例

### 7.1 Python实现：IPv4数据包解析

```python
import struct
import socket
from dataclasses import dataclass
from typing import Optional, List, Tuple
from enum import IntEnum

class IPProtocol(IntEnum):
    """IP协议号"""
    ICMP = 1
    IGMP = 2
    TCP = 6
    UDP = 17
    ENCAP = 41  # IPv6
    OSPF = 89

@dataclass
class IPv4Header:
    """IPv4首部"""
    version: int
    ihl: int
    tos: int
    total_length: int
    identification: int
    flags: int
    fragment_offset: int
    ttl: int
    protocol: IPProtocol
    checksum: int
    src_ip: str
    dst_ip: str
    options: bytes

    @property
    def header_length(self) -> int:
        """首部长度（字节）"""
        return self.ihl * 4

    @property
    def df(self) -> bool:
        """Don't Fragment标志"""
        return bool(self.flags & 0x02)

    @property
    def mf(self) -> bool:
        """More Fragments标志"""
        return bool(self.flags & 0x01)

    def __str__(self) -> str:
        return (f"IPv4 Header:\n"
                f"  Version: {self.version}\n"
                f"  IHL: {self.ihl} ({self.header_length} bytes)\n"
                f"  TOS: 0x{self.tos:02x}\n"
                f"  Total Length: {self.total_length}\n"
                f"  Identification: 0x{self.identification:04x}\n"
                f"  Flags: DF={self.df}, MF={self.mf}\n"
                f"  Fragment Offset: {self.fragment_offset * 8}\n"
                f"  TTL: {self.ttl}\n"
                f"  Protocol: {self.protocol.name} ({self.protocol.value})\n"
                f"  Checksum: 0x{self.checksum:04x}\n"
                f"  Source: {self.src_ip}\n"
                f"  Destination: {self.dst_ip}")

class IPv4Parser:
    """IPv4数据包解析器"""

    @staticmethod
    def parse_ip_address(addr_bytes: bytes) -> str:
        """解析IP地址"""
        return '.'.join(str(b) for b in addr_bytes)

    @staticmethod
    def ip_to_bytes(ip_str: str) -> bytes:
        """IP地址转字节"""
        return bytes(int(octet) for octet in ip_str.split('.'))

    @staticmethod
    def calculate_checksum(data: bytes) -> int:
        """计算IP校验和"""
        if len(data) % 2 == 1:
            data += b'\x00'

        s = 0
        for i in range(0, len(data), 2):
            w = (data[i] << 8) + data[i + 1]
            s += w

        s = (s >> 16) + (s & 0xffff)
        s = ~s & 0xffff
        return s

    @classmethod
    def parse(cls, packet: bytes) -> Tuple[IPv4Header, bytes]:
        """解析IPv4数据包"""
        if len(packet) < 20:
            raise ValueError("Packet too short for IPv4 header")

        # 解析固定首部
        version_ihl = packet[0]
        version = (version_ihl >> 4) & 0x0f
        ihl = version_ihl & 0x0f

        if version != 4:
            raise ValueError(f"Not an IPv4 packet: version={version}")

        if ihl < 5:
            raise ValueError(f"Invalid IHL: {ihl}")

        header_len = ihl * 4

        tos = packet[1]
        total_length = struct.unpack('!H', packet[2:4])[0]
        identification = struct.unpack('!H', packet[4:6])[0]

        flags_offset = struct.unpack('!H', packet[6:8])[0]
        flags = (flags_offset >> 13) & 0x07
        fragment_offset = flags_offset & 0x1fff

        ttl = packet[8]
        protocol = IPProtocol(packet[9])
        checksum = struct.unpack('!H', packet[10:12])[0]

        src_ip = cls.parse_ip_address(packet[12:16])
        dst_ip = cls.parse_ip_address(packet[16:20])

        # 解析选项
        options = packet[20:header_len] if ihl > 5 else b''

        header = IPv4Header(
            version=version,
            ihl=ihl,
            tos=tos,
            total_length=total_length,
            identification=identification,
            flags=flags,
            fragment_offset=fragment_offset,
            ttl=ttl,
            protocol=protocol,
            checksum=checksum,
            src_ip=src_ip,
            dst_ip=dst_ip,
            options=options
        )

        payload = packet[header_len:]

        return header, payload

    @classmethod
    def build(cls,
              src_ip: str,
              dst_ip: str,
              protocol: IPProtocol,
              payload: bytes,
              ttl: int = 64,
              tos: int = 0,
              identification: Optional[int] = None) -> bytes:
        """构建IPv4数据包"""

        header_len = 20  # 无选项
        total_len = header_len + len(payload)

        if identification is None:
            import random
            identification = random.randint(0, 65535)

        # 构建首部（先不加校验和）
        header = struct.pack('!BBHHHBBH4s4s',
            (4 << 4) | 5,       # Version + IHL
            tos,                 # TOS
            total_len,           # Total Length
            identification,      # Identification
            0,                   # Flags + Fragment Offset
            ttl,                 # TTL
            protocol.value,      # Protocol
            0,                   # Checksum (placeholder)
            cls.ip_to_bytes(src_ip),
            cls.ip_to_bytes(dst_ip)
        )

        # 计算校验和
        checksum = cls.calculate_checksum(header)
        header = header[:10] + struct.pack('!H', checksum) + header[12:]

        return header + payload


class IPFragmentReassembler:
    """IP分片重组器"""

    def __init__(self):
        self.fragments: dict = {}  # (src, dst, id) -> list of fragments

    def add_fragment(self, header: IPv4Header, payload: bytes) -> Optional[bytes]:
        """添加分片，如果重组完成返回完整数据"""
        key = (header.src_ip, header.dst_ip, header.identification)

        offset = header.fragment_offset * 8
        is_last = not header.mf

        if key not in self.fragments:
            self.fragments[key] = []

        self.fragments[key].append({
            'offset': offset,
            'data': payload,
            'is_last': is_last
        })

        # 检查是否收到所有分片
        frags = self.fragments[key]
        frags.sort(key=lambda x: x['offset'])

        # 检查连续性
        expected_offset = 0
        has_last = False

        for frag in frags:
            if frag['offset'] != expected_offset:
                return None  # 还有分片未到
            expected_offset += len(frag['data'])
            if frag['is_last']:
                has_last = True

        if not has_last:
            return None  # 未收到最后一个分片

        # 重组完成
        reassembled = b''.join(f['data'] for f in frags)
        del self.fragments[key]

        return reassembled


# 使用示例
if __name__ == "__main__":
    # 示例：解析捕获的数据包
    sample_packet = bytes([
        0x45,  # Version=4, IHL=5
        0x00,  # TOS
        0x00, 0x3c,  # Total Length=60
        0x1c, 0x46,  # Identification
        0x40, 0x00,  # Flags=2(DF), Fragment Offset=0
        0x40,  # TTL=64
        0x01,  # Protocol=ICMP
        0x00, 0x00,  # Checksum (invalid for demo)
        192, 168, 1, 1,  # Source IP
        192, 168, 1, 2,  # Dest IP
        # ICMP Echo Request payload
        0x08, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x01,
        0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68,
    ])

    parser = IPv4Parser()
    header, payload = parser.parse(sample_packet)
    print(header)
    print(f"\nPayload ({len(payload)} bytes): {payload.hex()}")
```

### 7.2 C语言实现：IP校验和计算

```c
#include <stdint.h>
#include <arpa/inet.h>

/**
 * RFC 1071 - 计算IP校验和
 * 使用16位累加和，然后取反
 */
uint16_t ip_checksum(const void *data, size_t length) {
    const uint16_t *ptr = data;
    uint32_t sum = 0;

    // 16位累加
    while (length > 1) {
        sum += *ptr++;
        length -= 2;
    }

    // 处理奇数字节
    if (length == 1) {
        sum += *(const uint8_t *)ptr;
    }

    // 进位回卷
    while (sum >> 16) {
        sum = (sum & 0xffff) + (sum >> 16);
    }

    return (uint16_t)(~sum);
}

/**
 * 验证IP首部校验和
 * 返回0表示校验通过
 */
int ip_verify_checksum(const struct iphdr *ip) {
    uint16_t received = ip->check;
    uint16_t calculated;

    // 临时清零校验和字段
    ((struct iphdr *)ip)->check = 0;
    calculated = ip_checksum(ip, ip->ihl * 4);
    ((struct iphdr *)ip)->check = received;

    return (received == calculated) ? 0 : -1;
}

/**
 * 递增式校验和更新
 * 用于TTL递减时的快速校验和更新
 */
uint16_t ip_checksum_incr_update(uint16_t old_checksum,
                                  uint16_t old_value,
                                  uint16_t new_value) {
    uint32_t sum = ~old_checksum & 0xffff;
    sum += ~old_value & 0xffff;
    sum += new_value;

    while (sum >> 16) {
        sum = (sum & 0xffff) + (sum >> 16);
    }

    return ~sum;
}

/**
 * IP首部结构（Linux风格）
 */
struct iphdr {
#if defined(__LITTLE_ENDIAN_BITFIELD)
    uint8_t ihl:4, version:4;
#elif defined(__BIG_ENDIAN_BITFIELD)
    uint8_t version:4, ihl:4;
#else
#error "Endianness not defined"
#endif
    uint8_t tos;
    uint16_t tot_len;
    uint16_t id;
    uint16_t frag_off;
    uint8_t ttl;
    uint8_t protocol;
    uint16_t check;
    uint32_t saddr;
    uint32_t daddr;
};
```

### 7.3 形式化规约（TLA+风格）

```tla
------------------------------ MODULE IPv4 -----------------------------

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    MaxPacketSize,      \* 最大数据包大小
    MaxTTL,             \* 最大TTL值
    MTU,                \* 最大传输单元
    Hosts,              \* 主机集合
    Links               \* 链路集合

VARIABLES
    packets,            \* 在传输中的数据包
    hostState,          \* 主机状态
    routingTable        \* 路由表

\* IP地址类型
IPAddr == [octet: 0..255, octet2: 0..255, octet3: 0..255, octet4: 0..255]

\* IP首部类型
IPHeader == [
    version: {4},
    ihl: 5..15,
    tos: 0..255,
    totalLen: 20..MaxPacketSize,
    id: 0..65535,
    flags: 0..7,
    fragOffset: 0..8191,
    ttl: 0..MaxTTL,
    protocol: 0..255,
    checksum: 0..65535,
    srcAddr: IPAddr,
    dstAddr: IPAddr
]

\* 完整IP数据包
IPPacket == [
    header: IPHeader,
    payload: Seq(0..255)
]

\* 初始化
Init ==
    /\ packets = {}
    /\ hostState = [h \in Hosts |-> [buffer |-> << >>, received |-> {}]]
    /\ routingTable = [h \in Hosts |-> [d \in IPAddr |-> CHOOSE n \in Hosts : TRUE]]

\* 发送数据包
SendPacket(h, dst, payload) ==
    LET packet == [
        header |-> [
            version |-> 4,
            ihl |-> 5,
            tos |-> 0,
            totalLen |-> 20 + Len(payload),
            id |-> Random(65535),
            flags |-> 0,
            fragOffset |-> 0,
            ttl |-> MaxTTL,
            protocol |-> 6,  \* TCP
            checksum |-> CalculateChecksum(...),
            srcAddr |-> h.addr,
            dstAddr |-> dst
        ],
        payload |-> payload
    ]
    IN packets' = packets \union {packet}

\* 转发数据包
ForwardPacket(p) ==
    IF p.header.ttl > 1
    THEN
        LET nextHop == routingTable[p.srcAddr][p.header.dstAddr]
            newPacket == [
                header |-> [p.header EXCEPT !.ttl = @ - 1],
                payload |-> p.payload
            ]
        IN packets' = (packets \ {p}) \union {newPacket}
    ELSE packets' = packets \ {p}  \* TTL过期，丢弃

\* 分片操作
FragmentPacket(p, mtu) ==
    LET dataOffset == (p.header.ihl * 4)
        payloadSize == p.header.totalLen - dataOffset
        maxFragmentPayload == ((mtu - dataOffset) / 8) * 8
        numFragments == (payloadSize + maxFragmentPayload - 1) \div maxFragmentPayload

        Fragment(i) == [
            header |-> [
                p.header EXCEPT
                    !.totalLen = IF i < numFragments - 1
                                 THEN mtu
                                 ELSE dataOffset + (payloadSize - i * maxFragmentPayload),
                    !.fragOffset = i * (maxFragmentPayload / 8),
                    !.flags = IF i < numFragments - 1 THEN 1 ELSE 0  \* MF flag
            ],
            payload |-> SubSeq(p.payload,
                              i * maxFragmentPayload + 1,
                              Min((i + 1) * maxFragmentPayload, payloadSize))
        ]
    IN {Fragment(i) : i \in 0..numFragments-1}

\* 重组操作
ReassembleFragments(fragments) ==
    LET sorted == SortBy(fragments, LAMBDA f: f.header.fragOffset)
        totalPayload == Concatenate([f.payload : f \in sorted])
    IN [
        header |-> [
            (Head(sorted).header) EXCEPT
                !.totalLen = 20 + Len(totalPayload),
                !.fragOffset = 0,
                !.flags = 0
        ],
        payload |-> totalPayload
    ]

\* 安全属性
TypeInvariant ==
    /\ \A p \in packets : p \in IPPacket
    /\ \A h \in Hosts : hostState[h].buffer \in Seq(IPPacket)

\* 活性属性
PacketDelivery ==
    \A p \in packets :
        p.header.dstAddr \in Hosts /\ p.header.ttl > 0
        ~>
        p \in hostState[p.header.dstAddr].received

=============================================================================
```

---

## 8. 现代应用

### 8.1 IPv4现状与挑战

#### 8.1.1 地址枯竭

- IPv4地址空间（约43亿）已分配殆尽
- 缓解措施：NAT、CIDR、地址回收

#### 8.1.2 向IPv6过渡

- IPv6（RFC 2460）提供128位地址空间
- 双栈部署：同时运行IPv4和IPv6
- 隧道技术：6to4、Teredo、ISATAP

### 8.2 现代网络中的IP

| 应用场景 | IP角色 | 相关技术 |
|---------|--------|---------|
| 云计算 | 虚拟网络寻址 | VPC、SDN |
| 容器网络 | 容器间通信 | CNI、Calico、Flannel |
| SD-WAN | 智能路由选择 | 策略路由、BGP |
| IoT | 设备寻址 | 6LoWPAN、RPL |

### 8.3 与后续RFC的关系

| RFC | 主题 | 与RFC 791关系 |
|-----|------|--------------|
| RFC 1349 | ToS字段重新定义 | 更新服务类型语义 |
| RFC 1519 | CIDR | 扩展地址分配灵活性 |
| RFC 1918 | 私有地址 | 定义专用地址空间 |
| RFC 2474 | DSCP | 重新定义ToS字段为DiffServ |
| RFC 6864 | ID字段 | 修订Identification字段语义 |
| RFC 8200 | IPv6 | 下一代互联网协议 |

### 8.4 教学与研究的持续价值

尽管IPv6正在逐步部署，RFC 791仍然具有重要价值：

1. **基础理论**: 理解网络层设计的经典案例
2. **向后兼容**: 绝大多数网络仍支持IPv4
3. **工程思想**: 简洁、可扩展的设计哲学
4. **历史理解**: 互联网发展的关键技术节点

---

## 参考文献

1. Postel, J. (Ed.). "Internet Protocol." RFC 791, September 1981.
2. Braden, R. (Ed.). "Requirements for Internet Hosts -- Communication Layers." RFC 1122, October 1989.
3. Baker, F. "Requirements for IP Version 4 Routers." RFC 1812, June 1995.
4. Hinden, R. and S. Deering. "IP Version 6 Addressing Architecture." RFC 4291, February 2006.

---

_文档版本: 1.0_
_最后更新: 2026年_
_状态: 核心RFC映射完成_
