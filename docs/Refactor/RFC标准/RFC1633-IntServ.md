# RFC 1633 - Integrated Services in the Internet Architecture: an Overview

## 1. RFC概述

### 1.1 基本信息

- **RFC编号**: RFC 1633
- **标题**: Integrated Services in the Internet Architecture: an Overview
- **发布日期**: 1994年6月
- **状态**: Informational
- **作者**: R. Braden, D. Clark, S. Shenker
- **相关**: RFC 2210, RFC 2211, RFC 2212, RFC 2215

### 1.2 历史背景

1990年代初，互联网从学术研究网络向商业应用转变，实时应用（视频会议、IP电话）对服务质量（QoS）提出了新要求。RFC 1633提出了综合服务体系结构（IntServ），试图在传统尽力而为（Best-Effort）服务基础上提供服务质量保证。

### 1.3 核心贡献

- 提出综合服务体系结构框架
- 定义服务质量（QoS）概念
- 引入资源预留机制
- 建立基于流（Flow）的服务模型

---

## 2. 协议详细说明

### 2.1 IntServ架构

#### 2.1.1 体系结构

```
+------------------+     +------------------+     +------------------+
|    Application   |     |    Application   |     |    Application   |
|  (QoS Request)   |     |  (QoS Request)   |     |  (QoS Request)   |
+--------+---------+     +--------+---------+     +--------+---------+
         |                        |                        |
         v                        v                        v
+--------+---------+     +--------+---------+     +--------+---------+
|   RSVP (Signaling)|    |   RSVP (Signaling)|    |   RSVP (Signaling)|
|   Path/Resv msgs  |    |   Path/Resv msgs  |    |   Path/Resv msgs  |
+--------+---------+     +--------+---------+     +--------+---------+
         |                        |                        |
         v                        v                        v
+--------+---------+     +--------+---------+     +--------+---------+
|   Admission      |<--->|   Admission      |<--->|   Admission      |
|   Control        |     |   Control        |     |   Control        |
+--------+---------+     +--------+---------+     +--------+---------+
         |                        |                        |
         v                        v                        v
+--------+---------+     +--------+---------+     +--------+---------+
|   Packet         |<--->|   Packet         |<--->|   Packet         |
|   Classifier     |     |   Classifier     |     |   Classifier     |
+--------+---------+     +--------+---------+     +--------+---------+
         |                        |                        |
         v                        v                        v
+--------+---------+     +--------+---------+     +--------+---------+
|   Packet         |     |   Packet         |     |   Packet         |
|   Scheduler      |     |   Scheduler      |     |   Scheduler      |
+--------+---------+     +--------+---------+     +--------+---------+
         |                        |                        |
         v                        v                        v
+--------+---------+     +--------+---------+     +--------+---------+
|   Link Layer     |<--->|   Link Layer     |<--->|   Link Layer     |
+------------------+     +------------------+     +------------------+
```

#### 2.1.2 核心组件

| 组件 | 功能 | 实现 |
|------|------|------|
| 信令协议（RSVP） | 资源预留请求 | RSVP Path/Resv消息 |
| 准入控制 | 决定是否接受流 | 带宽检查、策略控制 |
| 分类器 | 识别数据包所属流 | 五元组匹配 |
| 调度器 | 按策略转发数据包 | WFQ、WF2Q+等 |

### 2.2 服务类型

#### 2.2.1 保证服务（Guaranteed Service）

- **RFC**: 2212
- **特点**: 提供确定的带宽、延迟和丢包保证
- **适用**: 硬实时应用
- **参数**:
  - 带宽保证
  - 延迟上界
  - 零丢包（拥塞时）

#### 2.2.2 可控负载服务（Controlled-Load Service）

- **RFC**: 2211
- **特点**: 在网络轻载时提供近似无拥塞服务
- **适用**: 自适应实时应用
- **保证**: 高概率的低延迟和低丢包

#### 2.2.3 尽力而为服务（Best-Effort）

- **特点**: 传统IP服务
- **适用**: 非实时应用
- **保证**: 无

### 2.3 流（Flow）概念

```
流的定义：
- 源IP地址
- 目的IP地址
- 源端口
- 目的端口
- 协议号

流标识：五元组 {src_ip, dst_ip, src_port, dst_port, protocol}
```

---

## 3. 报文格式

### 3.1 RSVP消息格式

```
RSVP Common Header:
 0                   1                   2                   3
 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
| Vers|  Flags  |  Msg Type |       RSVP Checksum             |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|  Send_TTL     | (Reserved)|           RSVP Length             |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+

Message Types:
  1 = Path
  2 = Resv
  3 = PathErr
  4 = ResvErr
  5 = PathTear
  6 = ResvTear
  7 = ResvConf
```

### 3.2 RSVP对象格式

```
RSVP Object Header:
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|             Length (bytes)    | Class-Num     |   C-Type      |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                                                               |
//                        Object Contents                      //
|                                                               |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+

Common Object Classes:
  Class-Num = 1:  NULL
  Class-Num = 3:  SESSION (dest addr, protocol, dst port)
  Class-Num = 4:  RSVP_HOP (previous hop address)
  Class-Num = 5:  INTEGRITY
  Class-Num = 6:  TIME_VALUES (refresh period)
  Class-Num = 7:  ERROR_SPEC
  Class-Num = 8:  SCOPE
  Class-Num = 9:  STYLE
  Class-Num = 10: FLOWSPEC
  Class-Num = 11: FILTER_SPEC
  Class-Num = 12: SENDER_TEMPLATE
  Class-Num = 13: SENDER_TSPEC
  Class-Num = 14: ADSPEC
  Class-Num = 15: POLICY_DATA
  Class-Num = 16: RESV_CONFIRM
```

### 3.3 FLOWSPEC格式（保证服务）

```
Service Number: 2 (Guaranteed Service)

Parameter 1: Token Bucket TSpec
  Token Rate (r):  bytes per second
  Bucket Depth (b): bytes
  Peak Rate (p):   bytes per second
  Minimum Policed Unit (m): bytes
  Maximum Packet Size (M): bytes

Parameter 2: Guaranteed Service RSpec
  Rate (R):        reserved bandwidth
  Slack Term (S):  delay slack
```

### 3.4 PATH消息流程

```
Client              Router A            Router B            Server
  |                    |                   |                   |
  | ---- PATH -------->|                   |                   |
  |    SENDER_TSPEC    |                   |                   |
  |    (r, b, p, m, M) |                   |                   |
  |                    | ---- PATH ------> |                   |
  |                    |    ADSPEC         |                   |
  |                    |    (path char)    |                   |
  |                    |                   | ---- PATH ------> |
  |                    |                   |                   |
  |                    |                   | <--- RESV ------- |
  |                    |                   |    FLOWSPEC       |
  |                    |                   |    (R, S)         |
  |                    | <--- RESV ------- |                   |
  |                    |    FLOWSPEC       |                   |
  | <--- RESV -------- |                   |                   |
  |    FLOWSPEC        |                   |                   |
  |                    |                   |                   |
```

---

## 4. 状态机

### 4.1 RSVP会话状态机

```
                    +------------------+
                    |      IDLE        |
                    |  (no reservation) |
                    +--------+---------+
                             |
                    Path msg received
                             |
                             v
                    +--------+---------+
                    |  PATH_RECEIVED   |
                    +--------+---------+
                             |
              +--------------+--------------+
              |                             |
        Local App                     Remote request
        requests reservation          (Resv msg)
              |                             |
              v                             v
    +---------+---------+      +----------+----------+
    |   LOCAL_REQ       |      |   RESV_RECEIVED     |
    +---------+---------+      +----------+----------+
              |                             |
              +--------------+--------------+
                             |
                        Admission check
                             |
              +--------------+--------------+
              |                             |
         Accept                         Reject
              |                             |
              v                             v
    +---------+---------+      +----------+----------+
    |   ESTABLISHED     |      |   REJECTED          |
    | (reservation      |      |   (error to app     |
    |  installed)       |      |    or sender)       |
    +---------+---------+      +----------+----------+
              |                             |
         Timeout/                        Timeout/
         Teardown                           Clear
              |                             |
              v                             v
    +---------+---------+      +----------+----------+
    |      IDLE         |<-----+      IDLE           |
    +-------------------+      +---------------------+
```

### 4.2 准入控制决策

```
                    +------------------+
                    |  Request Arrival |
                    +--------+---------+
                             |
                             v
                    +--------+---------+
                    | Parse FLOWSPEC   |
                    | Extract (r, b, R)|
                    +--------+---------+
                             |
                             v
                    +--------+---------+
                    | Check Available  |
                    | Bandwidth        |
                    +--------+---------+
                             |
              +--------------+--------------+
              |                             |
        Bandwidth OK                  Bandwidth NOK
              |                             |
              v                             v
    +---------+---------+      +----------+----------+
    | Check Buffer/     |      |  REJECT              |
    | Delay Constraints |      |  (RSVP ResvErr)      |
    +---------+---------+      +----------+----------+
              |                             |
    +---------+---------+                   |
    | Constraints OK?   |                   |
    +---------+---------+                   |
         | Yes                    |          |
         v                        |          |
    +---------+---------+         |          |
    |   ACCEPT          |         |          |
    | Install state in  |         |          |
    | packet scheduler  |         |          |
    +---------+---------+         |          |
              |                   |          |
              v                   v          v
    +---------+---------+      +----------+----------+
    | Send Resv to prev |      | Send ResvErr to    |
    | hop / Confirm app |      | sender             |
    +-------------------+      +--------------------+
```

---

## 5. 安全性考虑

### 5.1 IntServ安全威胁

#### 5.1.1 资源耗尽攻击

- **攻击方式**: 伪造大量RSVP请求预留资源
- **影响**: 合法流无法获得资源
- **缓解措施**:
  - 身份认证
  - 策略控制
  - 速率限制

#### 5.1.2 信令攻击

- **攻击方式**: 伪造RSVP错误消息
- **影响**: 合法预留被拆除
- **缓解措施**:
  - 消息完整性保护
  - 源地址验证

#### 5.1.3 窃取服务

- **攻击方式**: 未授权使用预留资源
- **影响**: 服务质量下降
- **缓解措施**:
  - 分类器严格匹配
  - 加密认证

### 5.2 RSVP安全机制

```
RSVP安全特性:

1. INTEGRITY对象
   - 提供消息完整性验证
   - 使用共享密钥或公钥

2. 身份认证
   - POLICY_DATA对象携带身份
   - 支持多种认证机制

3. 序列号
   - 防止重放攻击
   - 单调递增序列
```

---

## 6. 与教材对标的章节

### 6.1 《计算机网络：自顶向下方法》

| RFC 1633内容 | 对应章节 |
|-------------|----------|
| IntServ概述 | 第7章：多媒体网络 - 7.3 尽力而为服务的局限 |
| 服务质量 | 7.4 提供多种类型的服务 |
| RSVP协议 | 7.5 调度和监管机制（补充） |

### 6.2 《计算机网络》（谢希仁）

| RFC 1633内容 | 对应章节 |
|-------------|----------|
| IntServ模型 | 第8章：互联网上的音频/视频服务 |
| 综合服务 | 8.3.2 综合服务IntServ与资源预留协议RSVP |

### 6.3 《QoS for IP/MPLS Networks》

| RFC 1633内容 | 对应章节 |
|-------------|----------|
| IntServ架构 | 第3章：Integrated Services |
| RSVP信令 | 第4章：RSVP |
| 服务类型 | 第5章：Guaranteed and Controlled-Load Services |

---

## 7. 实现示例

### 7.1 Python实现：RSVP消息处理

```python
import struct
from dataclasses import dataclass
from typing import List, Optional, Dict
from enum import IntEnum

class RSVPMessageType(IntEnum):
    """RSVP消息类型"""
    PATH = 1
    RESV = 2
    PATH_ERR = 3
    RESV_ERR = 4
    PATH_TEAR = 5
    RESV_TEAR = 6
    RESV_CONFIRM = 7

class RSVPObjectClass(IntEnum):
    """RSVP对象类"""
    NULL = 0
    SESSION = 1
    RSVP_HOP = 3
    INTEGRITY = 4
    TIME_VALUES = 5
    ERROR_SPEC = 6
    SCOPE = 7
    STYLE = 8
    FLOWSPEC = 9
    FILTER_SPEC = 10
    SENDER_TEMPLATE = 11
    SENDER_TSPEC = 12
    ADSPEC = 13
    POLICY_DATA = 14
    RESV_CONFIRM = 15

class ServiceType(IntEnum):
    """服务类型"""
    NULL = 1
    CONTROLLED_LOAD = 5
    GUARANTEED = 2

@dataclass
class TokenBucketSpec:
    """令牌桶规范（TSpec）"""
    token_rate: float  # r: token bucket rate (bytes/sec)
    bucket_depth: int  # b: token bucket depth (bytes)
    peak_rate: float   # p: peak data rate (bytes/sec)
    min_policed_unit: int  # m: minimum policed unit (bytes)
    max_packet_size: int   # M: maximum packet size (bytes)

    def pack(self) -> bytes:
        """打包TSpec"""
        # Simplified packing - actual format is more complex
        data = struct.pack('>f', self.token_rate)
        data += struct.pack('>I', self.bucket_depth)
        data += struct.pack('>f', self.peak_rate)
        data += struct.pack('>II', self.min_policed_unit, self.max_packet_size)
        return data

    @classmethod
    def unpack(cls, data: bytes) -> 'TokenBucketSpec':
        """解包TSpec"""
        r = struct.unpack('>f', data[0:4])[0]
        b = struct.unpack('>I', data[4:8])[0]
        p = struct.unpack('>f', data[8:12])[0]
        m = struct.unpack('>I', data[12:16])[0]
        M = struct.unpack('>I', data[16:20])[0]
        return cls(r, b, p, m, M)

    def __str__(self) -> str:
        return (f"TSpec(r={self.token_rate:.2f} B/s, b={self.bucket_depth} B, "
                f"p={self.peak_rate:.2f} B/s, m={self.min_policed_unit}, M={self.max_packet_size})")

@dataclass
class RSVPObject:
    """RSVP对象"""
    class_num: int
    c_type: int
    data: bytes

    def pack(self) -> bytes:
        """打包对象"""
        length = 4 + len(self.data)
        header = struct.pack('>HBB', length, self.class_num, self.c_type)
        return header + self.data

    @classmethod
    def unpack(cls, data: bytes) -> 'RSVPObject':
        """解包对象"""
        length = struct.unpack('>H', data[0:2])[0]
        class_num = data[2]
        c_type = data[3]
        obj_data = data[4:length]
        return cls(class_num, c_type, obj_data)

@dataclass
class RSVPMessage:
    """RSVP消息"""
    version: int
    flags: int
    msg_type: RSVPMessageType
    checksum: int
    send_ttl: int
    length: int
    objects: List[RSVPObject]

    def pack(self) -> bytes:
        """打包RSVP消息"""
        # Build objects
        objects_data = b''.join(obj.pack() for obj in self.objects)

        # Calculate length
        self.length = 8 + len(objects_data)

        # Build header
        first_byte = (self.version << 4) | (self.flags & 0x0F)
        header = bytes([first_byte, self.msg_type])
        header += struct.pack('>H', self.checksum)
        header += bytes([self.send_ttl, 0])  # Reserved
        header += struct.pack('>H', self.length)

        return header + objects_data

    @classmethod
    def unpack(cls, data: bytes) -> 'RSVPMessage':
        """解包RSVP消息"""
        if len(data) < 8:
            raise ValueError("RSVP message too short")

        first_byte = data[0]
        version = first_byte >> 4
        flags = first_byte & 0x0F
        msg_type = RSVPMessageType(data[1])
        checksum = struct.unpack('>H', data[2:4])[0]
        send_ttl = data[4]
        length = struct.unpack('>H', data[6:8])[0]

        # Parse objects
        objects = []
        offset = 8
        while offset < length:
            obj_length = struct.unpack('>H', data[offset:offset+2])[0]
            obj = RSVPObject.unpack(data[offset:offset+obj_length])
            objects.append(obj)
            offset += obj_length

        return cls(version, flags, msg_type, checksum, send_ttl, length, objects)

    def __str__(self) -> str:
        return (f"RSVP {self.msg_type.name} (v{self.version}, "
                f"{len(self.objects)} objects, {self.length} bytes)")


class IntServRouter:
    """简化IntServ路由器实现"""

    def __init__(self, total_bandwidth: float):
        self.total_bandwidth = total_bandwidth
        self.reserved_bandwidth = 0.0
        self.flow_table: Dict[str, Dict] = {}  # Flow ID -> reservation info

    def admit_flow(self, tspec: TokenBucketSpec) -> bool:
        """准入控制决策"""
        required_bandwidth = tspec.token_rate

        # 检查带宽是否足够
        if self.reserved_bandwidth + required_bandwidth > self.total_bandwidth:
            print(f"[Admission] REJECT: insufficient bandwidth")
            print(f"  Required: {required_bandwidth:.2f} B/s")
            print(f"  Available: {self.total_bandwidth - self.reserved_bandwidth:.2f} B/s")
            return False

        # 检查其他资源（缓冲区、延迟约束等）
        # 简化：假设延迟约束满足

        print(f"[Admission] ACCEPT")
        print(f"  Bandwidth: {required_bandwidth:.2f} B/s reserved")
        return True

    def install_reservation(self, flow_id: str, tspec: TokenBucketSpec,
                           rspec: Optional[Dict] = None):
        """安装预留状态"""
        self.flow_table[flow_id] = {
            'tspec': tspec,
            'rspec': rspec,
            'bandwidth': tspec.token_rate
        }
        self.reserved_bandwidth += tspec.token_rate
        print(f"[Install] Reservation installed for flow {flow_id}")

    def remove_reservation(self, flow_id: str):
        """移除预留状态"""
        if flow_id in self.flow_table:
            self.reserved_bandwidth -= self.flow_table[flow_id]['bandwidth']
            del self.flow_table[flow_id]
            print(f"[Remove] Reservation removed for flow {flow_id}")

    def handle_path_message(self, msg: RSVPMessage) -> RSVPMessage:
        """处理PATH消息"""
        print(f"\n[RSVP] Received PATH message")

        # 提取SENDER_TSPEC
        tspec = None
        for obj in msg.objects:
            if obj.class_num == RSVPObjectClass.SENDER_TSPEC:
                # 简化解包
                tspec = TokenBucketSpec(10000, 1000, 20000, 20, 1500)
                break

        # 构建ADSPEC（路径特性）
        adspec = RSVPObject(
            class_num=RSVPObjectClass.ADSPEC,
            c_type=2,
            data=b'\x00' * 20  # 简化的ADSPEC
        )

        # 转发PATH消息（添加RSVP_HOP和ADSPEC）
        new_objects = msg.objects + [adspec]
        response = RSVPMessage(
            version=1,
            flags=0,
            msg_type=RSVPMessageType.PATH,
            checksum=0,
            send_ttl=msg.send_ttl - 1,
            length=0,
            objects=new_objects
        )

        return response

    def handle_resv_message(self, msg: RSVPMessage) -> bool:
        """处理RESV消息"""
        print(f"\n[RSVP] Received RESV message")

        # 提取FLOWSPEC
        flowspec = None
        for obj in msg.objects:
            if obj.class_num == RSVPObjectClass.FLOWSPEC:
                # 简化解包
                flowspec = {'rate': 10000, 'slack': 0}
                break

        if not flowspec:
            return False

        # 准入控制
        tspec = TokenBucketSpec(flowspec['rate'], 1000, 20000, 20, 1500)
        flow_id = "flow_1"  # 简化

        if self.admit_flow(tspec):
            self.install_reservation(flow_id, tspec, flowspec)
            return True
        else:
            return False

    def get_utilization(self) -> float:
        """获取带宽利用率"""
        return self.reserved_bandwidth / self.total_bandwidth * 100


# 使用示例
if __name__ == "__main__":
    print("=" * 60)
    print("IntServ/RSVP Protocol Implementation Demo")
    print("=" * 60)

    # 创建路由器（100KB/s总带宽）
    router = IntServRouter(total_bandwidth=100000)

    print(f"\nRouter initialized with {router.total_bandwidth} B/s bandwidth")

    # 1. 创建PATH消息
    print("\n1. PATH Message:")
    print("-" * 40)

    sender_tspec = RSVPObject(
        class_num=RSVPObjectClass.SENDER_TSPEC,
        c_type=2,
        data=TokenBucketSpec(10000, 1000, 20000, 20, 1500).pack()
    )

    sender_template = RSVPObject(
        class_num=RSVPObjectClass.SENDER_TEMPLATE,
        c_type=1,
        data=b'\x0a\x00\x00\x01\x0a\x00\x00\x02\x00\x00\x00\x00'  # src/dst IP
    )

    session = RSVPObject(
        class_num=RSVPObjectClass.SESSION,
        c_type=1,
        data=b'\x0a\x00\x00\x02\x11\x00\x00\x1f\x90'  # dst IP, proto, port
    )

    path_msg = RSVPMessage(
        version=1,
        flags=0,
        msg_type=RSVPMessageType.PATH,
        checksum=0,
        send_ttl=64,
        length=0,
        objects=[session, sender_template, sender_tspec]
    )

    print(f"Created: {path_msg}")
    print(f"Packed: {len(path_msg.pack())} bytes")

    # 处理PATH消息
    router.handle_path_message(path_msg)

    # 2. 创建RESV消息
    print("\n2. RESV Message:")
    print("-" * 40)

    flowspec = RSVPObject(
        class_num=RSVPObjectClass.FLOWSPEC,
        c_type=2,
        data=b'\x00\x00\x00\x02' + struct.pack('>f', 10000.0)  # Guaranteed service
    )

    style = RSVPObject(
        class_num=RSVPObjectClass.STYLE,
        c_type=1,
        data=struct.pack('>I', 0x10)  # WF style
    )

    resv_msg = RSVPMessage(
        version=1,
        flags=0,
        msg_type=RSVPMessageType.RESV,
        checksum=0,
        send_ttl=64,
        length=0,
        objects=[session, style, flowspec]
    )

    print(f"Created: {resv_msg}")

    # 处理RESV消息
    success = router.handle_resv_message(resv_msg)
    print(f"Reservation {'succeeded' if success else 'failed'}")

    print(f"\nCurrent utilization: {router.get_utilization():.1f}%")
```

---

## 8. 现代应用

### 8.1 IntServ的现状

#### 8.1.1 局限性

- **可扩展性问题**: 每个流状态维护开销大
- **核心网部署困难**: 互联网骨干网流数量巨大
- **RSVP复杂性**: 信令协议复杂
- **应用限制**: 主要用于企业网和专用网络

#### 8.1.2 替代方案

- **DiffServ（RFC 2474）**: 可扩展的区分服务
- **MPLS-TE**: 流量工程
- **SDN QoS**: 软件定义网络QoS

### 8.2 RSVP的演进

| 应用 | 描述 |
|------|------|
| MPLS-TE | RSVP-TE用于标签交换路径建立 |
| NSIS | 下一代信令协议（RFC 5974） |
| NSH | 服务链信令 |

### 8.3 与相关RFC的关系

| RFC | 主题 | 与RFC 1633关系 |
|-----|------|---------------|
| RFC 2205 | RSVP | 信令协议规范 |
| RFC 2210 | RSVP使用 | IntServ使用RSVP |
| RFC 2211 | 可控负载 | 服务规范 |
| RFC 2212 | 保证服务 | 服务规范 |
| RFC 2215 | 通用特性 | 通用参数定义 |
| RFC 2474 | DiffServ | 替代方案 |

### 8.4 教学与研究价值

1. **QoS基础**: 理解服务质量保证的基本概念
2. **资源预留**: 学习资源管理原理
3. **信令协议**: RSVP设计思想影响深远
4. **历史意义**: 理解互联网QoS发展历程

---

## 参考文献

1. Braden, R., Clark, D., and S. Shenker. "Integrated Services in the Internet Architecture: an Overview." RFC 1633, June 1994.
2. Braden, R., Ed., et al. "Resource ReSerVation Protocol (RSVP) -- Version 1 Functional Specification." RFC 2205, September 1997.
3. Shenker, S., Partridge, C., and R. Guerin. "Specification of Guaranteed Quality of Service." RFC 2212, September 1997.
4. Wroclawski, J. "Specification of the Controlled-Load Network Element Service." RFC 2211, September 1997.

---

_文档版本: 1.0_
_最后更新: 2026年_
_状态: 核心RFC映射完成_
