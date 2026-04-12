# RFC 793 - Transmission Control Protocol (TCP)

## 1. RFC概述

### 1.1 基本信息

- **RFC编号**: RFC 793
- **标题**: Transmission Control Protocol
- **发布日期**: 1981年9月
- **状态**: Internet Standard
- **替代**: RFC 761
- **更新**: RFC 1122, RFC 1323, RFC 2018, RFC 2581, RFC 5681, RFC 6298, RFC 7323

### 1.2 历史背景

RFC 793定义了传输控制协议（TCP），是互联网协议套件的核心协议之一。TCP提供了面向连接、可靠、基于字节流的传输服务，是当今互联网应用（Web、Email、FTP等）的基础。

### 1.3 核心贡献

- 定义了面向连接的可靠传输服务
- 引入流量控制和拥塞控制机制
- 确立了端到端原则
- 定义了端口概念实现多路复用

---

## 2. 协议详细说明

### 2.1 核心特性

#### 2.1.1 面向连接

- 数据传输前需要建立连接（三次握手）
- 连接是全双工的
- 数据传输完成后需要关闭连接（四次挥手）

#### 2.1.2 可靠性保证

- **序列号**: 为每个字节分配序列号
- **确认机制**: 累积确认已接收数据
- **重传机制**: 超时重传和快速重传
- **流量控制**: 滑动窗口机制
- **拥塞控制**: 避免网络拥塞

#### 2.1.3 字节流抽象

- 不保留消息边界
- 按序交付字节流
- 应用程序负责消息解析

### 2.2 核心机制

#### 2.2.1 连接管理

```
连接状态转换:
CLOSED → SYN-SENT → ESTABLISHED → FIN-WAIT-1 → FIN-WAIT-2 → TIME-WAIT → CLOSED
                ↑                                    ↓
                └────────── ESTABLISHED ←───────────┘
```

#### 2.2.2 滑动窗口

- **发送窗口**: 已发送但未确认的数据
- **接收窗口**: 可接收的数据量（通告窗口）
- **拥塞窗口**: 网络容量限制

#### 2.2.3 拥塞控制算法

- **慢启动**: 指数增长探测可用带宽
- **拥塞避免**: 线性增长维持稳定
- **快速重传**: 收到3个重复ACK立即重传
- **快速恢复**: 避免慢启动，保持拥塞窗口

---

## 3. 报文格式

### 3.1 TCP首部格式

```
 0                   1                   2                   3
 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|          Source Port          |       Destination Port        |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                        Sequence Number                        |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                    Acknowledgment Number                      |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|  Data |           |U|A|P|R|S|F|                               |
| Offset| Reserved  |R|C|S|S|Y|I|            Window             |
|       |           |G|K|H|T|N|N|                               |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|           Checksum            |         Urgent Pointer        |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                    Options (if Data Offset > 5)               |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                             data                              |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
```

### 3.2 首部字段详解

| 字段 | 长度 | 描述 |
|------|------|------|
| Source Port | 16 bits | 源端口号 |
| Destination Port | 16 bits | 目的端口号 |
| Sequence Number | 32 bits | 序列号，标识数据字节流位置 |
| Acknowledgment Number | 32 bits | 确认号，期望收到的下一个序列号 |
| Data Offset | 4 bits | 首部长度，单位为4字节字 |
| Reserved | 6 bits | 保留位，必须为0 |
| Control Flags | 6 bits | 控制位（URG,ACK,PSH,RST,SYN,FIN） |
| Window | 16 bits | 接收窗口大小 |
| Checksum | 16 bits | 校验和 |
| Urgent Pointer | 16 bits | 紧急数据指针 |
| Options | 可变 | 选项字段 |

### 3.3 控制标志位

| 标志 | 名称 | 功能 |
|------|------|------|
| URG | Urgent | 紧急指针有效 |
| ACK | Acknowledgment | 确认号有效 |
| PSH | Push | 推送数据到应用层 |
| RST | Reset | 重置连接 |
| SYN | Synchronize | 同步序列号 |
| FIN | Finish | 结束连接 |

### 3.4 TCP选项

| 选项类型 | 代码 | 描述 |
|---------|------|------|
| End of Option List | 0 | 选项列表结束 |
| No-Operation | 1 | 填充 |
| Maximum Segment Size | 2 | 最大段大小 |
| Window Scale | 3 | 窗口缩放因子 |
| SACK Permitted | 4 | 允许选择性确认 |
| SACK | 5 | 选择性确认数据 |
| Timestamps | 8 | 时间戳选项 |

---

## 4. 状态机

### 4.1 TCP连接状态机

```
                              +--------+
                    主动打开  | CLOSED |
                   +--------->|        |
                   |         +---+----+
                   |             |
        被动打开   |   发送SYN   |
       +----------+-------------+--------+
       |                              |
       v                              v
+------+------+                +------+-------+
|   LISTEN    |                |  SYN-SENT    |
+------+------+                +------+-------+
       |                              |
 收到SYN | 发送SYN+ACK                 | 收到SYN+ACK
       v                              v
+------+------+                +------+-------+
| SYN-RECEIVED|<---------------+  SYN-RECEIVED|
+------+------+                +------+-------+
       |                              |
 收到ACK|                        收到ACK
       v                              v
+------+------+                +------+-------+
| ESTABLISHED |<---------------+ ESTABLISHED  |
+------+------+                +------+-------+
       |                              |
 发送FIN|                        发送FIN
       v                              v
+------+------+                +------+-------+
|FIN-WAIT-1   |                | CLOSE-WAIT   |
+------+------+                +------+-------+
       |                              |
 收到FIN+ACK|                    发送FIN
 或收到ACK  v                              v
+------+------+                +------+-------+
|FIN-WAIT-2   |                | LAST-ACK     |
+------+------+                +------+-------+
       |                              |
 收到FIN  |                        收到ACK
       v                              v
+------+------+                +------+-------+
|TIME-WAIT    |                |   CLOSED     |
+------+------+                +--------------+
       |
 2MSL超时|
       v
+------+------+
|   CLOSED    |
+-------------+
```

### 4.2 状态详细说明

| 状态 | 描述 |
|------|------|
| CLOSED | 无连接状态 |
| LISTEN | 监听传入连接请求 |
| SYN-SENT | 已发送SYN，等待确认 |
| SYN-RECEIVED | 收到SYN并发送SYN+ACK，等待确认 |
| ESTABLISHED | 连接建立，数据传输中 |
| FIN-WAIT-1 | 已发送FIN，等待ACK或对方FIN |
| FIN-WAIT-2 | 收到FIN的ACK，等待对方FIN |
| CLOSE-WAIT | 收到对方FIN，等待应用关闭 |
| CLOSING | 双方同时关闭，等待对方ACK |
| LAST-ACK | 已发送FIN，等待最后ACK |
| TIME-WAIT | 等待2MSL确保对方收到ACK |

---

## 5. 安全性考虑

### 5.1 已知安全漏洞

#### 5.1.1 SYN Flood攻击

- **攻击方式**: 大量伪造源地址发送SYN包
- **影响**: 耗尽服务器半连接队列资源
- **缓解措施**:
  - SYN Cookies（RFC 4987）
  - SYN Proxy
  - 增加SYN队列大小

#### 5.1.2 序列号预测攻击

- **攻击方式**: 预测TCP序列号进行会话劫持
- **影响**: 伪造数据包注入连接
- **缓解措施**:
  - 随机化初始序列号
  - 使用加密协议（TLS）

#### 5.1.3 RST攻击

- **攻击方式**: 伪造RST包终止连接
- **影响**: 强制断开合法连接
- **缓解措施**: 连接认证机制

### 5.2 安全扩展

#### 5.2.1 TCP-AO（认证选项）

- RFC 5925定义TCP认证选项
- 使用MAC验证报文完整性
- 防止伪造和篡改

#### 5.2.2 TLS/SSL

- 在TCP之上提供加密传输
- 认证服务器和客户端身份
- 保护数据机密性和完整性

### 5.3 形式化安全分析

```
安全属性：

1. 连接唯一性：
   ∀c1, c2 ∈ Connection:
   (c1.src = c2.src ∧ c1.dst = c2.dst ∧ c1.state = ESTABLISHED)
   ⇒ c1 = c2

2. 序列号单调性：
   ∀p1, p2 ∈ Packets(c):
   time(p1) < time(p2) ⇒ seq(p1) ≤ seq(p2)

3. 确认有效性：
   ∀ack ∈ Acknowledgments:
   ack.number ≤ max{seq(p) + len(p) | p ∈ ReceivedPackets}
```

---

## 6. 与教材对标的章节

### 6.1 《计算机网络：自顶向下方法》

| RFC 793内容 | 对应章节 |
|------------|----------|
| TCP概述 | 第3章：运输层 - 3.5 TCP概述 |
| TCP连接管理 | 3.5.2 TCP连接管理 |
| TCP可靠传输 | 3.4.1 可靠数据传输原理 |
| TCP流量控制 | 3.5.5 流量控制 |
| TCP拥塞控制 | 3.6 拥塞控制原理 |

### 6.2 《TCP/IP详解 卷1：协议》

| RFC 793内容 | 对应章节 |
|------------|----------|
| TCP协议基础 | 第17章：TCP：传输控制协议 |
| TCP连接建立/终止 | 第18章：TCP连接的建立与终止 |
| TCP超时与重传 | 第21章：TCP的超时与重传 |
| TCP坚持定时器 | 第22章：TCP的坚持定时器 |
| TCP拥塞控制 | 第24章：TCP的未来和性能 |

### 6.3 《计算机网络》（谢希仁）

| RFC 793内容 | 对应章节 |
|------------|----------|
| TCP协议 | 第5章：运输层 - 5.5 TCP报文段的首部格式 |
| TCP可靠传输 | 5.6 TCP可靠传输的实现 |
| TCP流量控制 | 5.7 TCP的流量控制 |
| TCP拥塞控制 | 5.8 TCP的拥塞控制 |
| TCP连接管理 | 5.9 TCP的运输连接管理 |

---

## 7. 实现示例

### 7.1 Python实现：TCP状态机

```python
from enum import Enum, auto
from dataclasses import dataclass, field
from typing import Optional, Dict, List, Callable, Tuple
import struct
import hashlib
import time
import threading

class TCPState(Enum):
    """TCP连接状态"""
    CLOSED = auto()
    LISTEN = auto()
    SYN_SENT = auto()
    SYN_RECEIVED = auto()
    ESTABLISHED = auto()
    FIN_WAIT_1 = auto()
    FIN_WAIT_2 = auto()
    CLOSE_WAIT = auto()
    CLOSING = auto()
    LAST_ACK = auto()
    TIME_WAIT = auto()

class TCPFlags:
    """TCP标志位"""
    FIN = 0x01
    SYN = 0x02
    RST = 0x04
    PSH = 0x08
    ACK = 0x10
    URG = 0x20

    @classmethod
    def to_string(cls, flags: int) -> str:
        """将标志位转换为字符串"""
        result = []
        if flags & cls.FIN: result.append('FIN')
        if flags & cls.SYN: result.append('SYN')
        if flags & cls.RST: result.append('RST')
        if flags & cls.PSH: result.append('PSH')
        if flags & cls.ACK: result.append('ACK')
        if flags & cls.URG: result.append('URG')
        return '|'.join(result) if result else 'NONE'

@dataclass
class TCPHeader:
    """TCP首部"""
    src_port: int
    dst_port: int
    seq_num: int
    ack_num: int
    data_offset: int = 5  # 20 bytes header
    flags: int = 0
    window: int = 65535
    checksum: int = 0
    urgent_ptr: int = 0
    options: bytes = b''

    def pack(self) -> bytes:
        """打包TCP首部"""
        offset_flags = (self.data_offset << 12) | self.flags
        header = struct.pack('!HHIIHHHH',
            self.src_port,
            self.dst_port,
            self.seq_num & 0xFFFFFFFF,
            self.ack_num & 0xFFFFFFFF,
            offset_flags,
            self.window,
            self.checksum,
            self.urgent_ptr
        )
        return header + self.options

    @classmethod
    def unpack(cls, data: bytes) -> 'TCPHeader':
        """解包TCP首部"""
        if len(data) < 20:
            raise ValueError("TCP header too short")

        src_port, dst_port, seq_num, ack_num, offset_flags, window, checksum, urgent_ptr = \
            struct.unpack('!HHIIHHHH', data[:20])

        data_offset = (offset_flags >> 12) & 0x0F
        flags = offset_flags & 0x3F
        options = data[20:data_offset * 4] if data_offset > 5 else b''

        return cls(
            src_port=src_port,
            dst_port=dst_port,
            seq_num=seq_num,
            ack_num=ack_num,
            data_offset=data_offset,
            flags=flags,
            window=window,
            checksum=checksum,
            urgent_ptr=urgent_ptr,
            options=options
        )

@dataclass
class TCPSegment:
    """TCP段"""
    header: TCPHeader
    payload: bytes = b''

    def pack(self) -> bytes:
        """打包完整TCP段"""
        return self.header.pack() + self.payload

    @classmethod
    def unpack(cls, data: bytes) -> 'TCPSegment':
        """解包TCP段"""
        header = TCPHeader.unpack(data)
        payload = data[header.data_offset * 4:]
        return cls(header=header, payload=payload)

class TCPConnection:
    """TCP连接实现"""

    def __init__(self, local_addr: Tuple[str, int], remote_addr: Optional[Tuple[str, int]] = None):
        self.local_addr = local_addr
        self.remote_addr = remote_addr

        # 状态
        self.state = TCPState.CLOSED
        self.state_lock = threading.Lock()

        # 序列号
        self.iss = self._generate_isn()  # 初始发送序列号
        self.irs = 0  # 初始接收序列号
        self.snd_nxt = self.iss  # 下一个发送序列号
        self.snd_una = self.iss  # 未确认的发送序列号
        self.snd_wnd = 0  # 发送窗口
        self.rcv_nxt = 0  # 期望接收的下一个序列号
        self.rcv_wnd = 65535  # 接收窗口

        # 数据缓冲区
        self.send_buffer = bytearray()
        self.recv_buffer = bytearray()
        self.buffer_lock = threading.Lock()

        # 定时器
        self.rto = 1.0  # 重传超时（秒）
        self.srtt = 0.0  # 平滑往返时间
        self.rttvar = 0.0  # 往返时间方差
        self.timers: Dict[str, threading.Timer] = {}

        # 回调
        self.on_state_change: Optional[Callable[[TCPState, TCPState], None]] = None
        self.on_data_received: Optional[Callable[[bytes], None]] = None

        # 统计
        self.stats = {
            'segments_sent': 0,
            'segments_received': 0,
            'retransmissions': 0,
            'bytes_sent': 0,
            'bytes_received': 0
        }

    def _generate_isn(self) -> int:
        """生成初始序列号（ISN）"""
        # RFC 793: ISN是一个每4微秒递增的时钟
        # 实际实现通常使用随机化
        return int((time.time() * 1000000) % (2**32))

    def _transition_to(self, new_state: TCPState):
        """状态转换"""
        with self.state_lock:
            old_state = self.state
            self.state = new_state
            print(f"[TCP] State transition: {old_state.name} -> {new_state.name}")

            if self.on_state_change:
                self.on_state_change(old_state, new_state)

    def active_open(self, remote_addr: Tuple[str, int]):
        """主动打开连接（三次握手发起方）"""
        if self.state != TCPState.CLOSED:
            raise RuntimeError(f"Cannot active_open from state {self.state}")

        self.remote_addr = remote_addr
        self._transition_to(TCPState.SYN_SENT)

        # 发送SYN
        syn_segment = self._create_segment(
            flags=TCPFlags.SYN,
            seq=self.iss,
            ack=0
        )
        self._send_segment(syn_segment)

    def passive_open(self):
        """被动打开连接（服务器监听）"""
        if self.state != TCPState.CLOSED:
            raise RuntimeError(f"Cannot passive_open from state {self.state}")

        self._transition_to(TCPState.LISTEN)

    def close(self):
        """关闭连接"""
        with self.state_lock:
            if self.state == TCPState.ESTABLISHED:
                self._transition_to(TCPState.FIN_WAIT_1)
                fin_segment = self._create_segment(
                    flags=TCPFlags.FIN | TCPFlags.ACK,
                    seq=self.snd_nxt,
                    ack=self.rcv_nxt
                )
                self._send_segment(fin_segment)
                self.snd_nxt += 1
            elif self.state == TCPState.CLOSE_WAIT:
                self._transition_to(TCPState.LAST_ACK)
                fin_segment = self._create_segment(
                    flags=TCPFlags.FIN | TCPFlags.ACK,
                    seq=self.snd_nxt,
                    ack=self.rcv_nxt
                )
                self._send_segment(fin_segment)

    def send(self, data: bytes) -> int:
        """发送数据"""
        if self.state != TCPState.ESTABLISHED:
            raise RuntimeError(f"Cannot send in state {self.state}")

        with self.buffer_lock:
            self.send_buffer.extend(data)

        self._transmit_data()
        return len(data)

    def _transmit_data(self):
        """传输发送缓冲区数据"""
        with self.buffer_lock:
            while self.send_buffer and self.state == TCPState.ESTABLISHED:
                # 计算可发送的数据量
                window = min(self.snd_wnd, self.rcv_wnd)
                in_flight = self.snd_nxt - self.snd_una
                available = window - in_flight

                if available <= 0:
                    break

                # 获取要发送的数据
                to_send = bytes(self.send_buffer[:available])
                if not to_send:
                    break

                # 创建并发送数据段
                segment = self._create_segment(
                    flags=TCPFlags.PSH | TCPFlags.ACK,
                    seq=self.snd_nxt,
                    ack=self.rcv_nxt,
                    payload=to_send
                )
                self._send_segment(segment)

                self.snd_nxt += len(to_send)
                self.send_buffer = self.send_buffer[len(to_send):]

    def _create_segment(self, flags: int, seq: int, ack: int, payload: bytes = b'') -> TCPSegment:
        """创建TCP段"""
        header = TCPHeader(
            src_port=self.local_addr[1],
            dst_port=self.remote_addr[1] if self.remote_addr else 0,
            seq_num=seq,
            ack_num=ack,
            flags=flags,
            window=self.rcv_wnd
        )
        return TCPSegment(header=header, payload=payload)

    def _send_segment(self, segment: TCPSegment):
        """发送TCP段（模拟）"""
        self.stats['segments_sent'] += 1
        self.stats['bytes_sent'] += len(segment.payload)
        print(f"[TCP] SEND {TCPFlags.to_string(segment.header.flags)} "
              f"seq={segment.header.seq_num} ack={segment.header.ack_num} "
              f"len={len(segment.payload)}")

    def receive_segment(self, segment: TCPSegment):
        """接收并处理TCP段"""
        self.stats['segments_received'] += 1
        self.stats['bytes_received'] += len(segment.payload)

        header = segment.header
        print(f"[TCP] RECV {TCPFlags.to_string(header.flags)} "
              f"seq={header.seq_num} ack={header.ack_num} "
              f"len={len(segment.payload)}")

        # 状态机处理
        handler = getattr(self, f'_handle_{self.state.name.lower()}', None)
        if handler:
            handler(segment)

    def _handle_syn_sent(self, segment: TCPSegment):
        """处理SYN_SENT状态下的报文"""
        header = segment.header

        if header.flags & TCPFlags.ACK:
            # 检查ACK是否有效
            if header.ack_num <= self.iss or header.ack_num > self.snd_nxt:
                return  # 无效ACK，忽略或发送RST

            if header.flags & TCPFlags.SYN:
                # 收到SYN+ACK，连接建立
                self.irs = header.seq_num
                self.rcv_nxt = header.seq_num + 1
                self.snd_una = header.ack_num

                # 发送ACK
                ack_segment = self._create_segment(
                    flags=TCPFlags.ACK,
                    seq=self.snd_nxt,
                    ack=self.rcv_nxt
                )
                self._send_segment(ack_segment)

                self._transition_to(TCPState.ESTABLISHED)

    def _handle_established(self, segment: TCPSegment):
        """处理ESTABLISHED状态下的报文"""
        header = segment.header

        # 处理ACK
        if header.flags & TCPFlags.ACK:
            if self.snd_una < header.ack_num <= self.snd_nxt:
                self.snd_una = header.ack_num

        # 处理数据
        if segment.payload:
            expected_seq = self.rcv_nxt
            if header.seq_num == expected_seq:
                # 按序数据
                with self.buffer_lock:
                    self.recv_buffer.extend(segment.payload)
                self.rcv_nxt += len(segment.payload)

                if self.on_data_received:
                    self.on_data_received(segment.payload)
            # 发送ACK
            ack_segment = self._create_segment(
                flags=TCPFlags.ACK,
                seq=self.snd_nxt,
                ack=self.rcv_nxt
            )
            self._send_segment(ack_segment)

        # 处理FIN
        if header.flags & TCPFlags.FIN:
            self.rcv_nxt += 1
            self._transition_to(TCPState.CLOSE_WAIT)
            ack_segment = self._create_segment(
                flags=TCPFlags.ACK,
                seq=self.snd_nxt,
                ack=self.rcv_nxt
            )
            self._send_segment(ack_segment)

    def _handle_fin_wait_1(self, segment: TCPSegment):
        """处理FIN_WAIT_1状态下的报文"""
        header = segment.header

        if header.flags & TCPFlags.ACK:
            if header.ack_num == self.snd_nxt:  # ACK了我们的FIN
                if header.flags & TCPFlags.FIN:
                    # 同时关闭
                    self.rcv_nxt += 1
                    self._transition_to(TCPState.CLOSING)
                else:
                    self._transition_to(TCPState.FIN_WAIT_2)

        if header.flags & TCPFlags.FIN:
            self.rcv_nxt += 1
            ack_segment = self._create_segment(
                flags=TCPFlags.ACK,
                seq=self.snd_nxt,
                ack=self.rcv_nxt
            )
            self._send_segment(ack_segment)

    def _handle_fin_wait_2(self, segment: TCPSegment):
        """处理FIN_WAIT_2状态下的报文"""
        header = segment.header

        if header.flags & TCPFlags.FIN:
            self.rcv_nxt += 1
            self._transition_to(TCPState.TIME_WAIT)
            ack_segment = self._create_segment(
                flags=TCPFlags.ACK,
                seq=self.snd_nxt,
                ack=self.rcv_nxt
            )
            self._send_segment(ack_segment)
            # 启动2MSL定时器
            self._start_timer('time_wait', 60, self._time_wait_timeout)

    def _handle_time_wait(self, segment: TCPSegment):
        """处理TIME_WAIT状态下的报文"""
        # 重新启动2MSL定时器
        if 'time_wait' in self.timers:
            self.timers['time_wait'].cancel()
        self._start_timer('time_wait', 60, self._time_wait_timeout)

    def _time_wait_timeout(self):
        """TIME_WAIT超时"""
        self._transition_to(TCPState.CLOSED)

    def _start_timer(self, name: str, timeout: float, callback: Callable):
        """启动定时器"""
        if name in self.timers:
            self.timers[name].cancel()
        self.timers[name] = threading.Timer(timeout, callback)
        self.timers[name].start()

    def get_stats(self) -> Dict:
        """获取连接统计"""
        return self.stats.copy()


# 使用示例：三次握手模拟
if __name__ == "__main__":
    print("=" * 60)
    print("TCP Connection Establishment Simulation")
    print("=" * 60)

    # 服务器端
    server = TCPConnection(local_addr=("0.0.0.0", 80))
    server.passive_open()
    print(f"Server listening on port 80...\n")

    # 模拟收到SYN
    syn_segment = TCPSegment(
        header=TCPHeader(
            src_port=54321,
            dst_port=80,
            seq_num=1000,
            ack_num=0,
            flags=TCPFlags.SYN
        )
    )

    # 服务器响应SYN+ACK
    server.remote_addr = ("192.168.1.2", 54321)
    server.receive_segment(syn_segment)

    # 模拟收到ACK（完成三次握手）
    # 首先手动设置状态以便演示
    server.state = TCPState.SYN_RECEIVED
    server.irs = 1000
    server.rcv_nxt = 1001

    ack_segment = TCPSegment(
        header=TCPHeader(
            src_port=54321,
            dst_port=80,
            seq_num=1001,
            ack_num=server.snd_nxt,
            flags=TCPFlags.ACK
        )
    )
    server.receive_segment(ack_segment)

    print(f"\nConnection established!")
    print(f"Server state: {server.state.name}")
    print(f"\nStatistics: {server.get_stats()}")
```

### 7.2 拥塞控制算法实现

```python
from enum import Enum
from dataclasses import dataclass
from typing import Optional
import math

class CongestionState(Enum):
    """拥塞控制状态"""
    SLOW_START = "slow_start"
    CONGESTION_AVOIDANCE = "congestion_avoidance"
    FAST_RECOVERY = "fast_recovery"

@dataclass
class CongestionControl:
    """TCP拥塞控制实现（Reno算法）"""

    # 拥塞窗口
    cwnd: float = 1.0  # 初始为1个MSS
    ssthresh: float = 65535.0  # 慢启动阈值

    # 状态
    state: CongestionState = CongestionState.SLOW_START

    # 重复ACK计数
    dup_ack_count: int = 0

    # 发送和确认状态
    mss: int = 1460  # 最大段大小
    flight_size: int = 0  # 在途数据量

    # 统计
    segments_acked: int = 0
    congestion_events: int = 0

    def on_ack_received(self, acked_bytes: int, is_dup: bool = False):
        """收到ACK时的处理"""
        if is_dup:
            self._handle_dup_ack()
        else:
            self._handle_new_ack(acked_bytes)

    def _handle_new_ack(self, acked_bytes: int):
        """处理新的ACK"""
        self.dup_ack_count = 0

        if self.state == CongestionState.SLOW_START:
            # 慢启动：指数增长
            self.cwnd += self.mss

            # 检查是否达到阈值
            if self.cwnd >= self.ssthresh:
                self.state = CongestionState.CONGESTION_AVOIDANCE
                print(f"[CC] Entering Congestion Avoidance, cwnd={self.cwnd}")

        elif self.state == CongestionState.CONGESTION_AVOIDANCE:
            # 拥塞避免：线性增长
            self.cwnd += (self.mss * self.mss) / self.cwnd

        elif self.state == CongestionState.FAST_RECOVERY:
            # 快速恢复结束，进入拥塞避免
            self.cwnd = self.ssthresh
            self.state = CongestionState.CONGESTION_AVOIDANCE
            print(f"[CC] Fast Recovery complete, cwnd={self.cwnd}")

        self.segments_acked += 1

    def _handle_dup_ack(self):
        """处理重复ACK"""
        self.dup_ack_count += 1

        if self.state == CongestionState.SLOW_START or \
           self.state == CongestionState.CONGESTION_AVOIDANCE:
            if self.dup_ack_count == 3:
                # 快速重传触发
                self.ssthresh = max(self.cwnd / 2, 2 * self.mss)
                self.cwnd = self.ssthresh + 3 * self.mss
                self.state = CongestionState.FAST_RECOVERY
                self.congestion_events += 1
                print(f"[CC] Fast Retransmit triggered, ssthresh={self.ssthresh}")

        elif self.state == CongestionState.FAST_RECOVERY:
            # 快速恢复中，继续增加窗口
            self.cwnd += self.mss

    def on_timeout(self):
        """超时处理"""
        print(f"[CC] Timeout occurred")

        # RFC 5681: 超时后设置ssthresh为max(flight_size/2, 2*MSS)
        self.ssthresh = max(self.flight_size / 2, 2 * self.mss)
        self.cwnd = self.mss  # 重置为1个MSS
        self.state = CongestionState.SLOW_START
        self.dup_ack_count = 0
        self.congestion_events += 1

    def can_send(self, in_flight: int) -> bool:
        """检查是否可以发送新数据"""
        return in_flight < self.cwnd

    def get_send_window(self) -> int:
        """获取当前发送窗口"""
        return int(self.cwnd)

    def __str__(self) -> str:
        return (f"CongestionControl(state={self.state.value}, "
                f"cwnd={self.cwnd:.2f}, ssthresh={self.ssthresh:.2f})")


class CUBIC(CongestionControl):
    """CUBIC拥塞控制算法（RFC 8312）"""

    def __init__(self):
        super().__init__()
        self.c = 0.4  # CUBIC缩放因子
        self.beta = 0.7  # 乘法减少因子
        self.w_max = 0  # 上次拥塞时的窗口
        self.k = 0  # 无拥塞增长时间
        self.epoch_start = 0  # 纪元开始时间
        self.origin_point = 0  # 原点

    def _cubic_function(self, t: float) -> float:
        """CUBIC窗口增长函数"""
        return self.c * (t - self.k) ** 3 + self.w_max

    def _handle_new_ack(self, acked_bytes: int):
        """CUBIC的ACK处理"""
        self.dup_ack_count = 0

        if self.state == CongestionState.SLOW_START:
            # 慢启动阶段与Reno相同
            self.cwnd += self.mss
            if self.cwnd >= self.ssthresh:
                self.epoch_start = time.time()
                self.origin_point = self.cwnd
                self.w_max = self.cwnd
                self.k = math.cbrt(self.w_max * (1 - self.beta) / self.c)
                self.state = CongestionState.CONGESTION_AVOIDANCE

        elif self.state == CongestionState.CONGESTION_AVOIDANCE:
            # CUBIC增长阶段
            t = time.time() - self.epoch_start
            target = self._cubic_function(t)

            if self.cwnd < target:
                # 凹增长区域
                self.cwnd += (target - self.cwnd) * self.mss / self.cwnd
            else:
                # 凸增长区域
                self.cwnd += self.mss

        elif self.state == CongestionState.FAST_RECOVERY:
            self.cwnd = self.ssthresh
            self.epoch_start = time.time()
            self.origin_point = self.cwnd
            self.w_max = self.cwnd
            self.k = math.cbrt(self.w_max * (1 - self.beta) / self.c)
            self.state = CongestionState.CONGESTION_AVOIDANCE

    def on_timeout(self):
        """CUBIC超时处理"""
        self.w_max = self.cwnd
        self.ssthresh = max(self.cwnd * self.beta, 2 * self.mss)
        self.cwnd = self.mss
        self.state = CongestionState.SLOW_START
        self.dup_ack_count = 0
        self.epoch_start = 0
        self.congestion_events += 1


import time

# 使用示例
if __name__ == "__main__":
    print("=" * 60)
    print("TCP Congestion Control Simulation")
    print("=" * 60)

    # Reno算法演示
    cc = CongestionControl()
    print(f"\nInitial state: {cc}\n")

    # 模拟慢启动
    for i in range(10):
        cc.on_ack_received(1460)
        if i % 3 == 0:
            print(f"After ACK {i+1}: {cc}")

    # 模拟3个重复ACK（快速重传）
    print(f"\n--- Fast Retransmit Simulation ---")
    for i in range(4):
        cc.on_ack_received(0, is_dup=True)
    print(f"After 3 dup ACKs: {cc}")

    # 恢复ACK
    cc.on_ack_received(1460)
    print(f"After recovery ACK: {cc}")
```

---

## 8. 现代应用

### 8.1 TCP在现代网络中的演进

#### 8.1.1 高速网络优化

- **BBR**: Google开发的基于带宽和RTT的拥塞控制
- **DCTCP**: 数据中心TCP，使用ECN反馈
- **TCP Vegas**: 基于延迟的拥塞控制

#### 8.1.2 移动网络优化

- **MPTCP**: 多路径TCP（RFC 6824）
- **TCP Fast Open**: 减少连接建立延迟
- **TCP RACK**: 基于时间的快速恢复

### 8.2 TCP与其他协议的对比

| 特性 | TCP | UDP | QUIC |
|------|-----|-----|------|
| 连接类型 | 面向连接 | 无连接 | 面向连接 |
| 可靠性 | 可靠 | 不可靠 | 可靠 |
| 拥塞控制 | 有 | 无 | 有 |
| 安全性 | 需额外TLS | 无 | 内置加密 |
| 队头阻塞 | 有 | 无 | 流级别无 |

### 8.3 与后续RFC的关系

| RFC | 主题 | 与RFC 793关系 |
|-----|------|--------------|
| RFC 1122 | 主机要求 | 澄清和修正TCP实现 |
| RFC 1323 | 窗口缩放 | 扩展窗口大小到1GB |
| RFC 2018 | SACK | 选择性确认扩展 |
| RFC 2581 | 拥塞控制 | 标准化拥塞控制算法 |
| RFC 5681 | 拥塞控制更新 | 更新拥塞控制规范 |
| RFC 6298 | RTO计算 | 改进重传超时计算 |
| RFC 7323 | 时间戳 | 扩展时间戳选项 |
| RFC 8312 | CUBIC | 现代拥塞控制算法 |

### 8.4 教学与研究价值

1. **协议设计经典**: 可靠传输协议的典范设计
2. **状态机学习**: 复杂状态机的标准案例
3. **性能优化**: 拥塞控制研究的基础平台
4. **安全分析**: 协议安全漏洞研究的重要对象

---

## 参考文献

1. Postel, J. (Ed.). "Transmission Control Protocol." RFC 793, September 1981.
2. Allman, M., Paxson, V., and E. Blanton. "TCP Congestion Control." RFC 5681, September 2009.
3. Ha, S., Rhee, I., and L. Xu. "CUBIC for Fast Long-Distance Networks." RFC 8312, February 2018.
4. Stevens, W.R. "TCP/IP Illustrated, Volume 1: The Protocols." Addison-Wesley, 1994.

---

_文档版本: 1.0_
_最后更新: 2026年_
_状态: 核心RFC映射完成_
