# RFC 2474 - Definition of the Differentiated Services Field (DS Field) in the IPv4 and IPv6 Headers

## 1. RFC概述

### 1.1 基本信息
- **RFC编号**: RFC 2474
- **标题**: Definition of the Differentiated Services Field (DS Field) in the IPv4 and IPv6 Headers
- **发布日期**: 1998年12月
- **状态**: Proposed Standard
- **废弃**: RFC 1349 (Type of Service)
- **相关**: RFC 2475, RFC 2597, RFC 2598, RFC 3246

### 1.2 历史背景
随着互联网规模扩大，IntServ的可扩展性问题日益突出。RFC 2474提出了区分服务（DiffServ）架构，将复杂的QoS功能从核心网络边缘化，核心网络仅执行简单的聚合流分类和转发，实现了更好的可扩展性。

### 1.3 核心贡献
- 重新定义IPv4 ToS字段为DS字段
- 定义区分服务代码点（DSCP）
- 建立逐跳行为（PHB）框架
- 提供可扩展的QoS解决方案

---

## 2. 协议详细说明

### 2.1 DiffServ架构

#### 2.1.1 边缘-核心模型
```
                          DiffServ Domain
    +----------------------------------------------------------------+
    |                                                                |
    |   Edge                  Core                    Edge            |
    |  +------+            +------+               +------+           |
    |  |Class-|            |Class-|               |Class-|           |
    |  |ifier |            |ifier |               |ifier |           |
    |  +--+---+            +--+---+               +--+---+           |
    |     |                   |                      |               |
    |     v                   v                      v               |
    |  +--+---+  Meter  +----+----+             +----+---+          |
    |  |Marker|<------>| Scheduler|            | Shaper  |          |
    |  +--+---+        +----+----+             +----+---+          |
    |     |                 |                      |               |
    |     v                 v                      v               |
    |  +--+---+            +--+---+               +--+---+           |
    |  |Queue |            |Queue |               |Queue |           |
    |  +------+            +------+               +------+           |
    |                                                                |
    +----------------------------------------------------------------+

    Edge Functions (Complex):        Core Functions (Simple):
    - Traffic Classification          - Traffic Classification
    - Traffic Metering                - Traffic Scheduling
    - Traffic Marking                 - Queue Management
    - Traffic Shaping
    - Admission Control
```

#### 2.1.2 边界路由器功能

| 功能 | 描述 | 实现 |
|------|------|------|
| 分类器 | 根据多重字段识别流 | 基于SA/DA/Port/Proto |
| 测量器 | 测量流量是否符合规格 | 令牌桶/漏桶算法 |
| 标记器 | 设置DSCP值 | 根据测量结果重标记 |
| 整形器 | 平滑突发流量 | 缓冲和速率控制 |
| 丢弃器 | 丢弃超额流量 | 尾部丢弃/RED |

#### 2.1.3 核心路由器功能

| 功能 | 描述 |
|------|------|
| 分类器 | 基于DSCP分类 |
| 调度器 | 根据PHB转发分组 |
| 队列管理 | AQM（主动队列管理） |

### 2.2 DS字段定义

#### 2.2.1 IPv4/IPv6 DS字段

```
IPv4首部（原ToS字段改为DS字段）:
 0   1   2   3   4   5   6   7
+---+---+---+---+---+---+---+---+
|         DSCP          |  CU   |
+---+---+---+---+---+---+---+---+

DSCP: Differentiated Services Code Point (6 bits)
CU:   Currently Unused (2 bits)

IPv6 Traffic Class字段:
 0   1   2   3   4   5   6   7
+---+---+---+---+---+---+---+---+
|         DSCP          |  CU   |
+---+---+---+---+---+---+---+---+
```

#### 2.2.2 DSCP值分配

| DSCP值 | 名称 | 用途 |
|--------|------|------|
| 000000 (0) | CS0 | 默认/尽力而为 |
| 001000 (8) | CS1 | 类别1（优先级） |
| 010000 (16) | CS2 | 类别2 |
| 011000 (24) | CS3 | 类别3 |
| 100000 (32) | CS4 | 类别4 |
| 101000 (40) | CS5 | 类别5 |
| 110000 (48) | CS6 | 类别6（网控） |
| 111000 (56) | CS7 | 类别7（网控） |
| 101110 (46) | EF | 加速转发 |
| 001010 (10) | AF11 | 确保转发类1低丢弃 |
| 001100 (12) | AF12 | 确保转发类1中丢弃 |
| 001110 (14) | AF13 | 确保转发类1高丢弃 |
| 010010 (18) | AF21 | 确保转发类2低丢弃 |
| 010100 (20) | AF22 | 确保转发类2中丢弃 |
| 010110 (22) | AF23 | 确保转发类2高丢弃 |
| 011010 (26) | AF31 | 确保转发类3低丢弃 |
| 011100 (28) | AF32 | 确保转发类3中丢弃 |
| 011110 (30) | AF33 | 确保转发类3高丢弃 |
| 100010 (34) | AF41 | 确保转发类4低丢弃 |
| 100100 (36) | AF42 | 确保转发类4中丢弃 |
| 100110 (38) | AF43 | 确保转发类4高丢弃 |

### 2.3 逐跳行为（PHB）

#### 2.3.1 默认PHB（Default PHB）
- **DSCP**: 000000 (0)
- **行为**: 传统尽力而为服务
- **要求**: 至少一个队列可用

#### 2.3.2 加速转发PHB（EF PHB）
- **RFC**: 3246
- **DSCP**: 101110 (46)
- **特点**: 低延迟、低抖动、低丢包
- **适用**: 语音、视频等实时应用
- **机制**: 优先级队列 + 速率限制

```
EF PHB特性:
- 配置速率R
- 配置突发B
- 保证带宽R
- 延迟上界 B/R
- 严格的优先级调度
```

#### 2.3.3 确保转发PHB组（AF PHB Group）
- **RFC**: 2597
- **类别**: 4个类别（AF1x-AF4x）
- **丢弃优先级**: 每个类别3个级别

```
AF PHB转发行为:

类1: AF11(10), AF12(12), AF13(14)  <-- 优先级递增
类2: AF21(18), AF22(20), AF23(22)
类3: AF31(26), AF32(28), AF33(30)
类4: AF41(34), AF42(36), AF43(38)

         低优先级业务      高优先级业务
              |                |
              v                v
        +----------+      +----------+
        |  AF13    |      |  AF43    |  <-- 高丢弃优先级
        |  (RED)   |      |  (RED)   |
        +----------+      +----------+
        |  AF12    |      |  AF42    |
        |  (RED)   |      |  (RED)   |
        +----------+      +----------+
        |  AF11    |      |  AF41    |  <-- 低丢弃优先级
        |  (RED)   |      |  (RED)   |
        +----------+      +----------+
              |                |
              v                v
        [ 加权公平调度 ]  [ 加权公平调度 ]
```

---

## 3. 报文格式

### 3.1 IPv4首部DS字段位置

```
 0                   1                   2                   3
 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|Version|  IHL  |      DS       |          Total Length         |
|       |       |     Field     |                               |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|         Identification        |Flags|      Fragment Offset    |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|  Time to Live |    Protocol   |         Header Checksum       |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                       Source Address                          |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                    Destination Address                        |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+

DS Field位置: 第2字节（原ToS字段）
DSCP: bits 0-5
ECN:  bits 6-7 (RFC 3168)
```

### 3.2 IPv6首部DS字段位置

```
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|Version| Traffic Class |           Flow Label                  |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|         Payload Length        |  Next Header  |   Hop Limit   |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                                                               |
+                                                               +
|                                                               |
+                     Source Address                            +
|                                                               |
+                                                               +
|                                                               |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                                                               |
+                                                               +
|                                                               |
+                  Destination Address                          +
|                                                               |
+                                                               +
|                                                               |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+

Traffic Class位置: bits 4-11
DSCP: bits 4-9 (前6位)
ECN:  bits 10-11 (后2位)
```

### 3.3 DSCP编码

```
DSCP编码格式:

Class Selector (CS):
  000 000 = CS0  (Default)
  001 000 = CS1  (Priority)
  010 000 = CS2  (Immediate)
  011 000 = CS3  (Flash)
  100 000 = CS4  (Flash Override)
  101 000 = CS5  (Critical)
  110 000 = CS6  (Internetwork Control)
  111 000 = CS7  (Network Control)

Assured Forwarding (AF):
  Class 1: 001 010 = AF11 (10)
           001 100 = AF12 (12)
           001 110 = AF13 (14)
  Class 2: 010 010 = AF21 (18)
           010 100 = AF22 (20)
           010 110 = AF23 (22)
  Class 3: 011 010 = AF31 (26)
           011 100 = AF32 (28)
           011 110 = AF33 (30)
  Class 4: 100 010 = AF41 (34)
           100 100 = AF42 (36)
           100 110 = AF43 (38)

Expedited Forwarding (EF):
  101 110 = EF (46)
```

---

## 4. 状态机

### 4.1 DiffServ边缘节点处理状态机

```
                    +------------------+
                    |   PACKET ARRIVAL |
                    +--------+---------+
                             |
                             v
                    +--------+---------+
                    | CLASSIFY         |
                    | (MF or BA)       |
                    +--------+---------+
                             |
              +--------------+--------------+
              |                             |
        Known Class                  Unknown Class
              |                             |
              v                             v
    +---------+---------+      +----------+----------+
    | METER             |      |  MARK Default       |
    | (Token Bucket)    |      |  (DSCP=0)           |
    +---------+---------+      +----------+----------+
              |                             |
    +---------+---------+                   |
    | In-profile?       |                   |
    +---------+---------+                   |
         | Yes         | No                |
         v             v                   |
    +----+----+   +----+------+             |
    | MARK    |   | MARK      |             |
    | (DSCP)  |   | (Downmark)|             |
    +----+----+   +----+------+             |
         |             |                   |
         +-------------+-------------------+
                             |
                             v
                    +--------+---------+
                    | POLICY CHECK     |
                    | (optional)       |
                    +--------+---------+
                             |
              +--------------+--------------+
              |                             |
         Policy OK                  Policy Violation
              |                             |
              v                             v
    +---------+---------+      +----------+----------+
    | FORWARD           |      |  DROP or            |
    | (to core)         |      |  REROUTE            |
    +-------------------+      +---------------------+
```

### 4.2 令牌桶算法状态机

```
                    +------------------+
                    |   INITIALIZE     |
                    |   bucket = B     |
                    |   last_time = t0 |
                    +--------+---------+
                             |
                             v
                    +--------+---------+
                    |   WAIT PACKET    |
                    +--------+---------+
                             |
                    Packet arrives (size S)
                             |
                             v
                    +--------+---------+
                    | UPDATE BUCKET    |
                    | bucket +=        |
                    |   r * (t - last) |
                    | bucket = min(b, B)|
                    | last_time = t    |
                    +--------+---------+
                             |
                             v
                    +--------+---------+
                    | CHECK BUCKET     |
                    | bucket >= S ?    |
                    +--------+---------+
                             |
              +--------------+--------------+
              | Yes                         | No
              v                             v
    +---------+---------+      +----------+----------+
    | CONFORMING        |      | NON-CONFORMING      |
    | bucket -= S       |      | (Mark / Drop /      |
    | Mark in-profile   |      |  Delay)             |
    +---------+---------+      +----------+----------+
              |                             |
              +--------------+--------------+
                             |
                             v
                    +--------+---------+
                    |   FORWARD        |
                    +--------+---------+
                             |
                             v
                    +--------+---------+
                    |   WAIT PACKET    |<---+
                    +------------------+    |
                             ^              |
                             +--------------+
```

---

## 5. 安全性考虑

### 5.1 DiffServ安全威胁

#### 5.1.1 DSCP欺骗
- **攻击方式**: 发送方标记高优先级DSCP
- **影响**: 抢占他人带宽资源
- **缓解措施**: 
  - 边缘路由器重写DSCP
  - 流量合约检查
  - 源地址验证

#### 5.1.2 拒绝服务
- **攻击方式**: 洪水攻击高优先级类别
- **影响**: 合法高优先级流量受损
- **缓解措施**: 
  - 每类别速率限制
  - 准入控制
  - 异常检测

#### 5.1.3 域间攻击
- **攻击方式**: 跨DS域发送标记流量
- **影响**: 违反服务合约
- **缓解措施**: 
  - 域间信任协商
  - DSCP重映射
  - SLA监控

### 5.2 安全最佳实践

```
DiffServ安全配置:

1. 边缘保护
   - 所有进入流量在边缘重新标记
   - 严格检查流量合约
   - 限制每流/每类带宽

2. 核心保护
   - 仅信任内部DSCP标记
   - 实施聚合速率限制
   - 监控异常流量模式

3. 域间安全
   - 建立信任边界
   - 协商DSCP映射
   - 监控SLA合规性
```

---

## 6. 与教材对标的章节

### 6.1 《计算机网络：自顶向下方法》
| RFC 2474内容 | 对应章节 |
|-------------|----------|
| DiffServ概述 | 第7章：多媒体网络 - 7.5 区分服务 |
| DSCP | 7.5.1 DiffServ体系结构 |
| PHB | 7.5.2 逐跳行为 |
| 边缘-核心 | 7.5.3 边界和核心功能 |

### 6.2 《计算机网络》（谢希仁）
| RFC 2474内容 | 对应章节 |
|-------------|----------|
| DiffServ | 第8章：互联网上的音频/视频服务 - 8.3.3 区分服务DiffServ |
| DS字段 | 4.2.3 IP数据报的格式（DS字段位置） |

### 6.3 《QoS for IP/MPLS Networks》
| RFC 2474内容 | 对应章节 |
|-------------|----------|
| DiffServ架构 | 第6章：DiffServ QoS |
| DSCP | 6.1 DiffServ Architecture |
| PHB | 6.2 Per-Hop Behaviors |

---

## 7. 实现示例

### 7.1 Python实现：DiffServ分类器和标记器

```python
import struct
from dataclasses import dataclass
from typing import Optional, Tuple
from enum import IntEnum
import time

class DSCP(IntEnum):
    """DSCP值定义"""
    # 默认
    CS0 = 0
    DEFAULT = 0
    
    # 类别选择器
    CS1 = 8
    CS2 = 16
    CS3 = 24
    CS4 = 32
    CS5 = 40
    CS6 = 48
    CS7 = 56
    
    # 确保转发
    AF11 = 10
    AF12 = 12
    AF13 = 14
    AF21 = 18
    AF22 = 20
    AF23 = 22
    AF31 = 26
    AF32 = 28
    AF33 = 30
    AF41 = 34
    AF42 = 36
    AF43 = 38
    
    # 加速转发
    EF = 46

class PHBType(IntEnum):
    """PHB类型"""
    DEFAULT = 0
    EF = 1
    AF = 2
    CS = 3

@dataclass
class TokenBucket:
    """令牌桶流量测量器"""
    rate: float       # 令牌产生速率 (bytes/sec)
    burst: int        # 桶容量 (bytes)
    
    def __post_init__(self):
        self.tokens = float(self.burst)  # 当前令牌数
        self.last_update = time.time()
    
    def consume(self, packet_size: int) -> Tuple[bool, float]:
        """
        尝试消费令牌
        返回: (是否合规, 当前令牌数)
        """
        now = time.time()
        elapsed = now - self.last_update
        
        # 补充令牌
        self.tokens = min(self.burst, self.tokens + self.rate * elapsed)
        self.last_update = now
        
        # 检查是否足够
        if self.tokens >= packet_size:
            self.tokens -= packet_size
            return True, self.tokens
        else:
            return False, self.tokens
    
    def get_conformance(self, packet_size: int) -> str:
        """获取合规性状态"""
        conforming, tokens = self.consume(packet_size)
        if conforming:
            return "conforming"
        elif tokens > 0:
            return "partial"
        else:
            return "non-conforming"

@dataclass
class IPPacket:
    """简化IP数据报"""
    src_ip: str
    dst_ip: str
    src_port: int
    dst_port: int
    protocol: int
    dscp: int
    payload: bytes
    
    @classmethod
    def from_bytes(cls, data: bytes) -> 'IPPacket':
        """从字节解析IP数据报"""
        if len(data) < 20:
            raise ValueError("IP header too short")
        
        # 解析IP首部
        version_ihl = data[0]
        tos = data[1]  # DS字段
        dscp = tos >> 2
        
        src_ip = '.'.join(str(b) for b in data[12:16])
        dst_ip = '.'.join(str(b) for b in data[16:20])
        
        protocol = data[9]
        
        # 简化：假设UDP/TCP并解析端口
        header_len = (version_ihl & 0x0F) * 4
        payload = data[header_len:]
        
        if protocol in (6, 17) and len(payload) >= 4:  # TCP or UDP
            src_port = struct.unpack('>H', payload[0:2])[0]
            dst_port = struct.unpack('>H', payload[2:4])[0]
        else:
            src_port = 0
            dst_port = 0
        
        return cls(
            src_ip=src_ip,
            dst_ip=dst_ip,
            src_port=src_port,
            dst_port=dst_port,
            protocol=protocol,
            dscp=dscp,
            payload=payload
        )
    
    def to_bytes(self) -> bytes:
        """转换为字节"""
        # 简化：构建基本IP首部
        version_ihl = (4 << 4) | 5  # IPv4, IHL=5
        tos = self.dscp << 2
        
        src_bytes = bytes(int(o) for o in self.src_ip.split('.'))
        dst_bytes = bytes(int(o) for o in self.dst_ip.split('.'))
        
        header = struct.pack('>BBHHHBBH',
            version_ihl,
            tos,
            20 + len(self.payload),  # Total length
            0,  # Identification
            0,  # Flags + Fragment offset
            64,  # TTL
            self.protocol,
            0   # Checksum (ignored)
        )
        header += src_bytes + dst_bytes
        
        return header + self.payload
    
    def get_flow_id(self) -> str:
        """获取流标识"""
        return f"{self.src_ip}:{self.src_port}-{self.dst_ip}:{self.dst_port}-{self.protocol}"

class DiffServClassifier:
    """DiffServ分类器"""
    
    def __init__(self):
        # BA (Behavior Aggregate) 分类器: 基于DSCP
        self.ba_rules: dict = {}
        
        # MF (Multi-Field) 分类器: 基于多重字段
        self.mf_rules: list = []
    
    def add_ba_rule(self, dscp: int, phb: PHBType) -> None:
        """添加BA分类规则"""
        self.ba_rules[dscp] = phb
    
    def add_mf_rule(self, src_ip: Optional[str], dst_ip: Optional[str],
                    src_port: Optional[int], dst_port: Optional[int],
                    protocol: Optional[int], dscp: int) -> None:
        """添加MF分类规则"""
        self.mf_rules.append({
            'src_ip': src_ip,
            'dst_ip': dst_ip,
            'src_port': src_port,
            'dst_port': dst_port,
            'protocol': protocol,
            'dscp': dscp
        })
    
    def classify(self, packet: IPPacket) -> int:
        """
        分类数据包，返回目标DSCP
        1. 先尝试MF分类
        2. 然后BA分类
        3. 最后返回Default
        """
        # MF分类
        for rule in self.mf_rules:
            if self._match_mf(packet, rule):
                return rule['dscp']
        
        # BA分类
        if packet.dscp in self.ba_rules:
            return packet.dscp
        
        # 默认
        return DSCP.DEFAULT
    
    def _match_mf(self, packet: IPPacket, rule: dict) -> bool:
        """检查是否匹配MF规则"""
        if rule['src_ip'] and packet.src_ip != rule['src_ip']:
            return False
        if rule['dst_ip'] and packet.dst_ip != rule['dst_ip']:
            return False
        if rule['src_port'] and packet.src_port != rule['src_port']:
            return False
        if rule['dst_port'] and packet.dst_port != rule['dst_port']:
            return False
        if rule['protocol'] and packet.protocol != rule['protocol']:
            return False
        return True

class DiffServMarker:
    """DiffServ标记器"""
    
    def __init__(self):
        self.meters: dict = {}  # Flow ID -> TokenBucket
        self.marking_rules: dict = {}  # Flow ID -> (committed_dscp, excess_dscp)
    
    def add_traffic_profile(self, flow_id: str, rate: float, burst: int,
                           committed_dscp: int, excess_dscp: int):
        """添加流量规格"""
        self.meters[flow_id] = TokenBucket(rate, burst)
        self.marking_rules[flow_id] = (committed_dscp, excess_dscp)
    
    def mark(self, packet: IPPacket) -> IPPacket:
        """标记数据包"""
        flow_id = packet.get_flow_id()
        
        if flow_id not in self.meters:
            # 无流量规格，直接转发
            return packet
        
        meter = self.meters[flow_id]
        committed_dscp, excess_dscp = self.marking_rules[flow_id]
        
        # 测量
        conforming, _ = meter.consume(len(packet.payload))
        
        # 标记
        if conforming:
            packet.dscp = committed_dscp
        else:
            packet.dscp = excess_dscp
        
        return packet

class DiffServScheduler:
    """简化DiffServ调度器"""
    
    def __init__(self):
        self.queues: dict = {}  # DSCP -> Queue
        self.weights: dict = {}  # DSCP -> Weight (for WFQ)
    
    def configure_queue(self, dscp: int, weight: float):
        """配置队列权重"""
        self.weights[dscp] = weight
        self.queues[dscp] = []
    
    def enqueue(self, packet: IPPacket):
        """入队"""
        dscp = packet.dscp
        if dscp not in self.queues:
            dscp = DSCP.DEFAULT
        self.queues[dscp].append(packet)
    
    def dequeue(self) -> Optional[IPPacket]:
        """出队（简化WFQ）"""
        # 找到非空队列中权重最高的
        best_dscp = None
        best_weight = 0
        
        for dscp, queue in self.queues.items():
            if queue and self.weights.get(dscp, 0) > best_weight:
                best_dscp = dscp
                best_weight = self.weights[dscp]
        
        if best_dscp:
            return self.queues[best_dscp].pop(0)
        return None


# 使用示例
if __name__ == "__main__":
    print("=" * 60)
    print("DiffServ Protocol Implementation Demo")
    print("=" * 60)
    
    # 1. DSCP值展示
    print("\n1. DSCP Values:")
    print("-" * 40)
    
    print("  Class Selector (CS):")
    for i in range(8):
        dscp = i << 3
        print(f"    CS{i}: DSCP = {dscp} (0x{dscp:02x})")
    
    print("\n  Assured Forwarding (AF):")
    for cls in range(1, 5):
        for dp in range(1, 4):
            dscp = (cls << 5) | (dp << 1) | 0
            print(f"    AF{cls}{dp}: DSCP = {dscp} (0x{dscp:02x})")
    
    print(f"\n  Expedited Forwarding (EF): DSCP = {DSCP.EF} (0x{DSCP.EF:02x})")
    
    # 2. 令牌桶演示
    print("\n2. Token Bucket Meter:")
    print("-" * 40)
    
    meter = TokenBucket(rate=10000, burst=5000)  # 10KB/s, 5KB burst
    
    packet_sizes = [1500, 1500, 1500, 1500, 1500]
    for i, size in enumerate(packet_sizes):
        conforming, tokens = meter.consume(size)
        status = "CONFORM" if conforming else "EXCEED"
        print(f"  Packet {i+1} ({size}B): {status}, tokens={tokens:.0f}")
        time.sleep(0.1)  # 模拟间隔
    
    # 3. 分类和标记演示
    print("\n3. DiffServ Edge Processing:")
    print("-" * 40)
    
    # 创建分类器
    classifier = DiffServClassifier()
    classifier.add_mf_rule(
        src_ip=None,
        dst_ip=None,
        src_port=None,
        dst_port=5060,  # SIP
        protocol=17,    # UDP
        dscp=DSCP.EF    # 语音流量标记为EF
    )
    classifier.add_mf_rule(
        src_ip=None,
        dst_ip=None,
        src_port=None,
        dst_port=80,    # HTTP
        protocol=6,     # TCP
        dscp=DSCP.AF21  # 商务数据标记为AF21
    )
    
    # 创建标记器
    marker = DiffServMarker()
    marker.add_traffic_profile(
        flow_id="192.168.1.1:12345-10.0.0.1:5060-17",
        rate=64000,     # 64kbps
        burst=8000,     # 1KB burst
        committed_dscp=DSCP.EF,
        excess_dscp=DSCP.AF13
    )
    
    # 测试数据包
    test_packets = [
        IPPacket("192.168.1.1", "10.0.0.1", 12345, 5060, 17, 0, b'Voice' * 100),
        IPPacket("192.168.1.1", "10.0.0.1", 12345, 5060, 17, 0, b'Voice' * 200),
        IPPacket("192.168.1.1", "10.0.0.1", 12346, 80, 6, 0, b'HTTP GET' * 50),
        IPPacket("192.168.1.2", "10.0.0.2", 12347, 443, 6, 0, b'HTTPS' * 50),
    ]
    
    for pkt in test_packets:
        # 分类
        target_dscp = classifier.classify(pkt)
        print(f"\n  Flow: {pkt.src_ip}:{pkt.src_port} -> {pkt.dst_ip}:{pkt.dst_port}")
        print(f"  Target DSCP: {target_dscp} (0x{target_dscp:02x})")
        
        # 标记
        marked_pkt = marker.mark(pkt)
        print(f"  Final DSCP: {marked_pkt.dscp} (0x{marked_pkt.dscp:02x})")
```

---

## 8. 现代应用

### 8.1 DiffServ部署现状

#### 8.1.1 企业网络
- 语音/视频优先（EF）
- 关键业务数据（AF）
- 普通流量（Default）

#### 8.1.2 运营商网络
- 跨域DS域部署
- SLA保障
- 流量工程

### 8.2 DiffServ与MPLS结合

```
DSCP到MPLS EXP映射:

IP DSCP          MPLS EXP
-------          --------
EF (46)     ->   5 (Expedited)
AF41 (34)   ->   4
AF31 (26)   ->   3
AF21 (18)   ->   2
AF11 (10)   ->   1
Default     ->   0
```

### 8.3 与相关RFC的关系

| RFC | 主题 | 与RFC 2474关系 |
|-----|------|---------------|
| RFC 2475 | DiffServ架构 | 架构定义 |
| RFC 2597 | AF PHB | 确保转发 |
| RFC 2598 | EF PHB | 加速转发（已废弃，由3246替代） |
| RFC 3246 | EF PHB更新 | 加速转发更新 |
| RFC 3260 | 术语说明 | 术语澄清 |
| RFC 3168 | ECN | DS字段最后两位用于ECN |

### 8.4 教学与研究价值

1. **可扩展QoS**: 理解大规模网络QoS设计
2. **分类技术**: 学习流量分类方法
3. **调度算法**: 研究队列调度
4. **实际部署**: 理解运营商网络实践

---

## 参考文献

1. Nichols, K., Blake, S., Baker, F., and D. Black. "Definition of the Differentiated Services Field (DS Field) in the IPv4 and IPv6 Headers." RFC 2474, December 1998.
2. Blake, S., et al. "An Architecture for Differentiated Services." RFC 2475, December 1998.
3. Heinanen, J., et al. "Assured Forwarding PHB Group." RFC 2597, June 1999.
4. Davie, B., et al. "An Expedited Forwarding PHB (Per-Hop Behavior)." RFC 3246, March 2002.
5. Ramakrishnan, K., Floyd, S., and D. Black. "The Addition of Explicit Congestion Notification (ECN) to IP." RFC 3168, September 2001.

---

*文档版本: 1.0*  
*最后更新: 2026年*  
*状态: 核心RFC映射完成*
