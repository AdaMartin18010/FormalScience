# RFC 7540 - Hypertext Transfer Protocol Version 2 (HTTP/2)

## 1. RFC概述

### 1.1 基本信息

- **RFC编号**: RFC 7540
- **标题**: Hypertext Transfer Protocol Version 2 (HTTP/2)
- **发布日期**: 2015年5月
- **状态**: Proposed Standard
- **废弃**: RFC 9113 (HTTP/2已更新)
- **相关**: SPDY协议（Google）、RFC 7541 (HPACK)

### 1.2 历史背景

HTTP/2是HTTP协议的重大升级，起源于Google的SPDY协议。HTTP/1.1存在队头阻塞、头部冗余等问题，HTTP/2通过二进制分帧、多路复用、头部压缩等技术显著提升了性能。

### 1.3 核心贡献

- 二进制分帧层替代文本协议
- 多路复用解决队头阻塞
- HPACK头部压缩算法
- 服务器推送机制
- 流优先级控制

---

## 2. 协议详细说明

### 2.1 HTTP/2架构

```
+-------------------------------------------+
|              Application Layer            |
|         (HTTP Semantics: methods,         |
|          headers, request/response)       |
+-------------------------------------------+
|              HTTP/2 Layer                 |
|  +-------------------------------------+  |
|  |  HPACK Header Compression           |  |
|  +-------------------------------------+  |
|  +-------------------------------------+  |
|  |  Binary Framing Layer               |  |
|  |  - Streams multiplexing             |  |
|  |  - Flow control                     |  |
|  |  - Priority handling                |  |
|  +-------------------------------------+  |
+-------------------------------------------+
|              TLS Layer (optional)         |
|         (ALPN: h2, h2-14, etc.)           |
+-------------------------------------------+
|              TCP Layer                    |
+-------------------------------------------+
```

### 2.2 核心概念

#### 2.2.1 流（Stream）

- 双向字节流，承载HTTP消息
- 使用31位标识符
- 流ID由客户端（奇数）或服务器（偶数）发起

#### 2.2.2 帧（Frame）

- HTTP/2通信的最小单位
- 不同类型的帧承载不同信息
- 帧头9字节固定

#### 2.2.3 消息（Message）

- 完整的请求或响应
- 由HEADERS帧、CONTINUATION帧和DATA帧组成

### 2.3 与HTTP/1.1对比

| 特性 | HTTP/1.1 | HTTP/2 |
|------|----------|--------|
| 传输格式 | 文本 | 二进制 |
| 多路复用 | 不支持 | 支持 |
| 头部压缩 | 不支持（除SDCH） | HPACK |
| 服务器推送 | 不支持 | 支持 |
| 流优先级 | 不支持 | 支持 |
| 队头阻塞 | TCP层 | 解决（应用层） |

---

## 3. 报文格式

### 3.1 帧格式

```
+-----------------------------------------------+
|                 Frame Header (9 bytes)        |
+-----------------------------------------------+
| Length (24)   | Type (8)  | Flags (8)         |
+-----------------------------------------------+
|R|              Stream Identifier (31)         |
+-----------------------------------------------+
|                 Payload (*)                   |
+-----------------------------------------------+
```

### 3.2 帧首部字段

| 字段 | 长度 | 描述 |
|------|------|------|
| Length | 24 bits | 载荷长度（最大16,384字节，可协商） |
| Type | 8 bits | 帧类型 |
| Flags | 8 bits | 帧标志 |
| R | 1 bit | 保留位（必须为0） |
| Stream Identifier | 31 bits | 流标识符 |

### 3.3 帧类型

| 类型 | 编码 | 描述 |
|------|------|------|
| DATA | 0x0 | 传输流内容 |
| HEADERS | 0x1 | 开启流并发送头部块 |
| PRIORITY | 0x2 | 指定流优先级 |
| RST_STREAM | 0x3 | 终止流 |
| SETTINGS | 0x4 | 连接配置 |
| PUSH_PROMISE | 0x5 | 服务器推送预告 |
| PING | 0x6 | 连接保活检测 |
| GOAWAY | 0x7 | 连接终止通知 |
| WINDOW_UPDATE | 0x8 | 流量控制窗口更新 |
| CONTINUATION | 0x9 | 头部块延续 |

### 3.4 帧标志

**通用标志**:

| 标志 | 值 | 适用类型 | 描述 |
|------|-----|---------|------|
| END_STREAM | 0x1 | DATA, HEADERS | 流结束 |
| ACK | 0x1 | SETTINGS, PING | 确认 |
| END_HEADERS | 0x4 | HEADERS, PUSH_PROMISE, CONTINUATION | 头部结束 |
| PADDED | 0x8 | DATA, HEADERS, PUSH_PROMISE | 填充存在 |
| PRIORITY | 0x20 | HEADERS | 优先级存在 |

### 3.5 流标识符规则

```
流ID分配:
0x0          - 连接控制流（不用于请求）
0x1, 0x3...  - 客户端发起的流（奇数）
0x2, 0x4...  - 服务器发起的流（偶数）

流状态:
IDLE → OPEN → HALF_CLOSED_REMOTE → CLOSED
              ↓
        HALF_CLOSED_LOCAL → CLOSED
```

### 3.6 SETTINGS帧格式

```
+-----------------------------------------------+
|       Identifier (16)     |      Value (32)   |
+---------------------------+-------------------+
|       ... (重复)                              |
+-----------------------------------------------+
```

**SETTINGS参数**:

| 参数 | ID | 默认值 | 描述 |
|------|----|--------|------|
| SETTINGS_HEADER_TABLE_SIZE | 0x1 | 4096 | HPACK表大小 |
| SETTINGS_ENABLE_PUSH | 0x2 | 1 | 允许服务器推送 |
| SETTINGS_MAX_CONCURRENT_STREAMS | 0x3 | 无限制 | 最大并发流 |
| SETTINGS_INITIAL_WINDOW_SIZE | 0x4 | 65535 | 初始流控窗口 |
| SETTINGS_MAX_FRAME_SIZE | 0x5 | 16384 | 最大帧大小 |
| SETTINGS_MAX_HEADER_LIST_SIZE | 0x6 | 无限制 | 最大头部列表 |

### 3.7 HPACK头部压缩

**静态表（61项）**:

```
索引 | 头部名称          | 头部值
-----|-------------------|------------------
1    | :authority        |
2    | :method           | GET
3    | :method           | POST
4    | :path             | /
5    | :path             | /index.html
...
61   | www-authenticate  |
```

**动态表**:

- 连接级存储
- FIFO队列
- 大小可配置（SETTINGS_HEADER_TABLE_SIZE）

**索引表示**:

```
索引头部字段:
0   1   2   3   4   5   6   7
+---+---+---+---+---+---+---+---+
| 1 |        Index (7+)         |
+---+---------------------------+

字面头部字段（有索引）:
0   1   2   3   4   5   6   7
+---+---+---+---+---+---+---+---+
| 0 | 1 |      Index (6+)       |
+---+---+-----------------------+
| H |     Value Length (7+)     |
+---+---------------------------+
| Value String (Length octets)  |
+-------------------------------+

字面头部字段（无索引）:
0   1   2   3   4   5   6   7
+---+---+---+---+---+---+---+---+
| 0 | 1 | 0 | 0 | 0 | 0 | 0 | 0 |
+---+---+---+---+---+---+---+---+
| H |     Name Length (7+)      |
+---+---------------------------+
| Name String (Length octets)   |
+---+---------------------------+
| H |     Value Length (7+)     |
+---+---------------------------+
| Value String (Length octets)  |
+-------------------------------+
```

---

## 4. 状态机

### 4.1 流状态机

```
                    +------------------+
                    |      IDLE        |
                    +--------+---------+
                             |
        send/receive         | send/receive
        HEADERS (request)    | PUSH_PROMISE
                             |
              +--------------+--------------+
              |                             |
              v                             v
    +---------+---------+      +----------+----------+
    |      OPEN         |      |  RESERVED (local)   |
    |  (bidirectional   |      |  (server push)      |
    |   data exchange)  |      +----------+----------+
    +---------+---------+                 |
              |                           | send
              |                           | HEADERS
    +---------+---------+                 v
    |                   |      +----------+----------+
 send END_STREAM  recv   |      |  HALF_CLOSED        |
    |   END_STREAM      |      |  (remote)           |
    v                   v      +----------+----------
+---+---+         +-----+-----+             |
|HALF_  |         |HALF_      |             | recv
|CLOSED |         |CLOSED     |             | END_STREAM
|(local) |         |(remote)   |             v
+---+---+         +-----+-----+    +--------+---------+
    |                   |          |      CLOSED      |
    |  recv END_STREAM  |          +------------------+
    +---------+---------+
              |
              v
    +---------+---------+
    |      CLOSED       |
    +-------------------+
```

### 4.2 连接状态机

```
                    +------------------+
                    |      IDLE        |
                    |  (preface sent/  |
                    |   received)      |
                    +--------+---------+
                             |
                    Preface complete
                             |
                             v
                    +--------+---------+
                    |      OPEN        |
                    |  (SETTINGS       |
                    |   exchanged)     |
                    +--------+---------+
                             |
              +--------------+--------------+
              |                             |
         GOAWAY sent                   GOAWAY received
              |                             |
              v                             v
    +---------+---------+      +----------+----------+
    |   CLOSING         |      |    CLOSING          |
    |  (half-closed)    |      |   (half-closed)     |
    +---------+---------+      +----------+----------+
              |                             |
              +--------------+--------------+
                             |
                             v
                    +--------+---------+
                    |      CLOSED      |
                    +------------------+
```

---

## 5. 安全性考虑

### 5.1 HTTP/2安全特性

#### 5.1.1 强制TLS（de facto）

- 浏览器要求HTTP/2 over TLS
- ALPN协商协议版本
- 证书验证

#### 5.1.2 流量控制安全

- 窗口大小限制防止内存耗尽
- SETTINGS_MAX_FRAME_SIZE限制
- SETTINGS_MAX_CONCURRENT_STREAMS限制

### 5.2 已知安全漏洞

#### 5.2.1 慢速攻击

- **攻击方式**: 发送大量微小WINDOW_UPDATE帧
- **影响**: 服务器资源耗尽
- **缓解措施**: 最小窗口增量限制

#### 5.2.2 HPACK炸弹

- **攻击方式**: 利用HPACK编码的重复模式
- **影响**: 内存耗尽（压缩比极高）
- **缓解措施**: 头部大小限制、表大小限制

#### 5.2.3 RST_STREAM洪水

- **攻击方式**: 快速创建和取消流
- **影响**: CPU资源耗尽
- **缓解措施**: 流创建速率限制

### 5.3 安全最佳实践

```
HTTP/2安全配置:

1. 流限制
   - max_concurrent_streams: 100-200
   - max_header_list_size: 16KB-32KB

2. 帧限制
   - max_frame_size: 16384（默认）
   - 禁止动态调整过大

3. 流量控制
   - initial_window_size: 65535（默认）
   - 监控窗口更新频率

4. 超时设置
   - 连接空闲超时: 30s-5min
   - 流空闲超时: 10s-1min
```

---

## 6. 与教材对标的章节

### 6.1 《计算机网络：自顶向下方法》

| RFC 7540内容 | 对应章节 |
|-------------|----------|
| HTTP/2概述 | 第2章：应用层 - 2.2 Web和HTTP（补充材料） |
| 多路复用 | 2.2 非持续/持续连接对比 |
| 性能优化 | 课后扩展阅读 |

### 6.2 《HTTP/2 in Action》

| RFC 7540内容 | 对应章节 |
|-------------|----------|
| 二进制分帧 | 第2章：HTTP/2的帧与流 |
| HPACK | 第3章：HPACK压缩 |
| 多路复用 | 第4章：多路复用 |
| 服务器推送 | 第5章：服务器推送 |
| 优先级 | 第6章：流优先级 |

### 6.3 《High Performance Browser Networking》

| RFC 7540内容 | 对应章节 |
|-------------|----------|
| HTTP/2设计 | 第12章：HTTP/2 |
| 二进制协议 | 12.1 二进制分帧层 |
| 流与多路复用 | 12.2 流、消息、帧 |
| HPACK | 12.3 HPACK压缩 |

---

## 7. 实现示例

### 7.1 Python实现：HTTP/2帧解析器

```python
import struct
from dataclasses import dataclass
from typing import Optional, List, Dict
from enum import IntEnum

class FrameType(IntEnum):
    """HTTP/2帧类型"""
    DATA = 0x0
    HEADERS = 0x1
    PRIORITY = 0x2
    RST_STREAM = 0x3
    SETTINGS = 0x4
    PUSH_PROMISE = 0x5
    PING = 0x6
    GOAWAY = 0x7
    WINDOW_UPDATE = 0x8
    CONTINUATION = 0x9

class FrameFlags(IntEnum):
    """HTTP/2帧标志"""
    END_STREAM = 0x01
    ACK = 0x01  # For SETTINGS and PING
    END_HEADERS = 0x04
    PADDED = 0x08
    PRIORITY = 0x20

class ErrorCode(IntEnum):
    """HTTP/2错误码"""
    NO_ERROR = 0x0
    PROTOCOL_ERROR = 0x1
    INTERNAL_ERROR = 0x2
    FLOW_CONTROL_ERROR = 0x3
    SETTINGS_TIMEOUT = 0x4
    STREAM_CLOSED = 0x5
    FRAME_SIZE_ERROR = 0x6
    REFUSED_STREAM = 0x7
    CANCEL = 0x8
    COMPRESSION_ERROR = 0x9
    CONNECT_ERROR = 0xa
    ENHANCE_YOUR_CALM = 0xb
    INADEQUATE_SECURITY = 0xc
    HTTP_1_1_REQUIRED = 0xd

@dataclass
class HTTP2Frame:
    """HTTP/2帧"""
    type: FrameType
    flags: int
    stream_id: int
    payload: bytes

    HEADER_SIZE = 9

    @classmethod
    def unpack(cls, data: bytes) -> 'HTTP2Frame':
        """解包HTTP/2帧"""
        if len(data) < cls.HEADER_SIZE:
            raise ValueError("Frame header too short")

        # 解析首部
        length = struct.unpack('>I', b'\x00' + data[:3])[0]
        frame_type = data[3]
        flags = data[4]
        stream_id = struct.unpack('>I', data[5:9])[0] & 0x7FFFFFFF

        # 验证载荷长度
        if len(data) < cls.HEADER_SIZE + length:
            raise ValueError(f"Frame payload incomplete: expected {length}, got {len(data) - cls.HEADER_SIZE}")

        payload = data[cls.HEADER_SIZE:cls.HEADER_SIZE + length]

        return cls(
            type=FrameType(frame_type),
            flags=flags,
            stream_id=stream_id,
            payload=payload
        )

    def pack(self) -> bytes:
        """打包HTTP/2帧"""
        length = len(self.payload)
        if length > 0xFFFFFF:
            raise ValueError("Payload too large")

        header = struct.pack('>I', length)[1:]  # 3 bytes
        header += struct.pack('>B', self.type)
        header += struct.pack('>B', self.flags)
        header += struct.pack('>I', self.stream_id & 0x7FFFFFFF)

        return header + self.payload

    def has_flag(self, flag: FrameFlags) -> bool:
        """检查是否设置了指定标志"""
        return bool(self.flags & flag)

    def __str__(self) -> str:
        flag_names = []
        if self.has_flag(FrameFlags.END_STREAM):
            flag_names.append('END_STREAM')
        if self.has_flag(FrameFlags.END_HEADERS):
            flag_names.append('END_HEADERS')
        if self.has_flag(FrameFlags.PADDED):
            flag_names.append('PADDED')
        if self.has_flag(FrameFlags.PRIORITY):
            flag_names.append('PRIORITY')
        if self.has_flag(FrameFlags.ACK) and self.type in (FrameType.SETTINGS, FrameType.PING):
            flag_names.append('ACK')

        return (f"HTTP2Frame(type={self.type.name}, flags=[{', '.join(flag_names)}], "
                f"stream_id={self.stream_id}, payload_len={len(self.payload)})")


@dataclass
class SettingsFrame:
    """SETTINGS帧解析"""
    settings: Dict[int, int]

    SETTING_HEADER_TABLE_SIZE = 0x1
    SETTING_ENABLE_PUSH = 0x2
    SETTING_MAX_CONCURRENT_STREAMS = 0x3
    SETTING_INITIAL_WINDOW_SIZE = 0x4
    SETTING_MAX_FRAME_SIZE = 0x5
    SETTING_MAX_HEADER_LIST_SIZE = 0x6

    SETTING_NAMES = {
        0x1: "HEADER_TABLE_SIZE",
        0x2: "ENABLE_PUSH",
        0x3: "MAX_CONCURRENT_STREAMS",
        0x4: "INITIAL_WINDOW_SIZE",
        0x5: "MAX_FRAME_SIZE",
        0x6: "MAX_HEADER_LIST_SIZE"
    }

    @classmethod
    def from_frame(cls, frame: HTTP2Frame) -> 'SettingsFrame':
        """从帧解析SETTINGS"""
        if frame.type != FrameType.SETTINGS:
            raise ValueError("Not a SETTINGS frame")

        settings = {}
        payload = frame.payload

        # ACK帧无载荷
        if frame.has_flag(FrameFlags.ACK):
            return cls(settings)

        # 解析设置项
        i = 0
        while i < len(payload):
            if i + 6 > len(payload):
                raise ValueError("Invalid SETTINGS payload")

            identifier = struct.unpack('>H', payload[i:i+2])[0]
            value = struct.unpack('>I', payload[i+2:i+6])[0]
            settings[identifier] = value
            i += 6

        return cls(settings)

    def to_frame(self, ack: bool = False, stream_id: int = 0) -> HTTP2Frame:
        """转换为SETTINGS帧"""
        if ack:
            return HTTP2Frame(
                type=FrameType.SETTINGS,
                flags=FrameFlags.ACK,
                stream_id=stream_id,
                payload=b''
            )

        payload = b''
        for identifier, value in self.settings.items():
            payload += struct.pack('>H', identifier)
            payload += struct.pack('>I', value)

        return HTTP2Frame(
            type=FrameType.SETTINGS,
            flags=0,
            stream_id=stream_id,
            payload=payload
        )

    def __str__(self) -> str:
        lines = ["SETTINGS:"]
        for identifier, value in self.settings.items():
            name = self.SETTING_NAMES.get(identifier, f"UNKNOWN({identifier})")
            lines.append(f"  {name} = {value}")
        return '\n'.join(lines)


@dataclass
class WindowUpdateFrame:
    """WINDOW_UPDATE帧"""
    window_size_increment: int

    @classmethod
    def from_frame(cls, frame: HTTP2Frame) -> 'WindowUpdateFrame':
        """从帧解析WINDOW_UPDATE"""
        if frame.type != FrameType.WINDOW_UPDATE:
            raise ValueError("Not a WINDOW_UPDATE frame")

        if len(frame.payload) != 4:
            raise ValueError("Invalid WINDOW_UPDATE payload size")

        increment = struct.unpack('>I', frame.payload)[0] & 0x7FFFFFFF
        return cls(window_size_increment=increment)

    def to_frame(self, stream_id: int = 0) -> HTTP2Frame:
        """转换为WINDOW_UPDATE帧"""
        payload = struct.pack('>I', self.window_size_increment & 0x7FFFFFFF)
        return HTTP2Frame(
            type=FrameType.WINDOW_UPDATE,
            flags=0,
            stream_id=stream_id,
            payload=payload
        )


@dataclass
class GoawayFrame:
    """GOAWAY帧"""
    last_stream_id: int
    error_code: ErrorCode
    debug_data: bytes

    @classmethod
    def from_frame(cls, frame: HTTP2Frame) -> 'GoawayFrame':
        """从帧解析GOAWAY"""
        if frame.type != FrameType.GOAWAY:
            raise ValueError("Not a GOAWAY frame")

        if len(frame.payload) < 8:
            raise ValueError("Invalid GOAWAY payload")

        last_stream_id = struct.unpack('>I', frame.payload[0:4])[0] & 0x7FFFFFFF
        error_code = struct.unpack('>I', frame.payload[4:8])[0]
        debug_data = frame.payload[8:]

        return cls(
            last_stream_id=last_stream_id,
            error_code=ErrorCode(error_code),
            debug_data=debug_data
        )

    def __str__(self) -> str:
        return (f"GOAWAY: last_stream_id={self.last_stream_id}, "
                f"error={self.error_code.name}, debug_data={self.debug_data!r}")


class HPACKDecoder:
    """简单的HPACK解码器"""

    STATIC_TABLE = [
        (':authority', ''),
        (':method', 'GET'),
        (':method', 'POST'),
        (':path', '/'),
        (':path', '/index.html'),
        (':scheme', 'https'),
        (':status', '200'),
        (':status', '204'),
        (':status', '206'),
        (':status', '304'),
        (':status', '400'),
        (':status', '404'),
        (':status', '500'),
        ('accept-charset', ''),
        ('accept-encoding', 'gzip, deflate'),
        ('accept-language', ''),
        ('accept-ranges', ''),
        ('accept', ''),
        ('access-control-allow-origin', ''),
        ('age', ''),
        ('allow', ''),
        ('authorization', ''),
        ('cache-control', ''),
        ('content-disposition', ''),
        ('content-encoding', ''),
        ('content-language', ''),
        ('content-length', ''),
        ('content-location', ''),
        ('content-range', ''),
        ('content-type', ''),
        ('cookie', ''),
        ('date', ''),
        ('etag', ''),
        ('expect', ''),
        ('expires', ''),
        ('from', ''),
        ('host', ''),
        ('if-match', ''),
        ('if-modified-since', ''),
        ('if-none-match', ''),
        ('if-range', ''),
        ('if-unmodified-since', ''),
        ('last-modified', ''),
        ('link', ''),
        ('location', ''),
        ('max-forwards', ''),
        ('proxy-authenticate', ''),
        ('proxy-authorization', ''),
        ('range', ''),
        ('referer', ''),
        ('refresh', ''),
        ('retry-after', ''),
        ('server', ''),
        ('set-cookie', ''),
        ('strict-transport-security', ''),
        ('transfer-encoding', ''),
        ('user-agent', ''),
        ('vary', ''),
        ('via', ''),
        ('www-authenticate', ''),
    ]

    def __init__(self, max_table_size: int = 4096):
        self.max_table_size = max_table_size
        self.dynamic_table: List[tuple] = []
        self.table_size = 0

    def decode(self, data: bytes) -> List[tuple]:
        """解码HPACK头部块"""
        headers = []
        i = 0

        while i < len(data):
            byte = data[i]

            # 索引头部字段（1xxxxxxx）
            if byte & 0x80:
                index, i = self._decode_integer(data, i, 7)
                name, value = self._get_from_table(index)
                headers.append((name, value))

            # 字面头部字段（01xxxxxx）- 有索引
            elif byte & 0xC0 == 0x40:
                index, i = self._decode_integer(data, i, 6)
                if index == 0:
                    name, i = self._decode_string(data, i)
                else:
                    name, _ = self._get_from_table(index)
                value, i = self._decode_string(data, i)
                headers.append((name, value))
                self._add_to_dynamic_table(name, value)

            # 字面头部字段（0000xxxx）- 无索引
            elif byte & 0xF0 == 0x00:
                index, i = self._decode_integer(data, i, 4)
                if index == 0:
                    name, i = self._decode_string(data, i)
                else:
                    name, _ = self._get_from_table(index)
                value, i = self._decode_string(data, i)
                headers.append((name, value))

            # 字面头部字段（0001xxxx）- 永不索引
            elif byte & 0xF0 == 0x10:
                index, i = self._decode_integer(data, i, 4)
                if index == 0:
                    name, i = self._decode_string(data, i)
                else:
                    name, _ = self._get_from_table(index)
                value, i = self._decode_string(data, i)
                headers.append((name, value))

            # 动态表大小更新（001xxxxx）
            elif byte & 0xE0 == 0x20:
                size, i = self._decode_integer(data, i, 5)
                self._update_table_size(size)

            else:
                raise ValueError(f"Invalid HPACK encoding at byte {i}: {byte:02x}")

        return headers

    def _decode_integer(self, data: bytes, index: int, prefix_bits: int) -> tuple:
        """解码HPACK整数"""
        mask = (1 << prefix_bits) - 1
        value = data[index] & mask
        index += 1

        if value < mask:
            return value, index

        # 多字节编码
        m = 0
        while True:
            if index >= len(data):
                raise ValueError("Integer encoding incomplete")
            byte = data[index]
            value += (byte & 0x7F) << m
            m += 7
            index += 1
            if not (byte & 0x80):
                break

        return value, index

    def _decode_string(self, data: bytes, index: int) -> tuple:
        """解码HPACK字符串"""
        huffman = bool(data[index] & 0x80)
        length, index = self._decode_integer(data, index, 7)

        if index + length > len(data):
            raise ValueError("String length exceeds data")

        string_data = data[index:index + length]
        index += length

        if huffman:
            # 简化：实际应使用Huffman解码
            string = string_data.decode('latin-1')
        else:
            string = string_data.decode('latin-1')

        return string, index

    def _get_from_table(self, index: int) -> tuple:
        """从静态表或动态表获取"""
        if index == 0:
            raise ValueError("Index 0 is not valid")

        if index <= len(self.STATIC_TABLE):
            return self.STATIC_TABLE[index - 1]

        dynamic_index = index - len(self.STATIC_TABLE) - 1
        if dynamic_index < len(self.dynamic_table):
            return self.dynamic_table[dynamic_index]

        raise ValueError(f"Index {index} not found in table")

    def _add_to_dynamic_table(self, name: str, value: str):
        """添加到动态表"""
        entry_size = len(name) + len(value) + 32

        # 确保有足够空间
        while self.table_size + entry_size > self.max_table_size and self.dynamic_table:
            removed = self.dynamic_table.pop()
            self.table_size -= len(removed[0]) + len(removed[1]) + 32

        if entry_size <= self.max_table_size:
            self.dynamic_table.insert(0, (name, value))
            self.table_size += entry_size

    def _update_table_size(self, size: int):
        """更新动态表大小限制"""
        self.max_table_size = size
        while self.table_size > self.max_table_size and self.dynamic_table:
            removed = self.dynamic_table.pop()
            self.table_size -= len(removed[0]) + len(removed[1]) + 32


# 使用示例
if __name__ == "__main__":
    print("=" * 60)
    print("HTTP/2 Protocol Implementation Demo")
    print("=" * 60)

    # 1. 帧解析示例
    print("\n1. HTTP/2 Frame Parsing:")
    print("-" * 40)

    # 构造一个SETTINGS帧
    settings = SettingsFrame(settings={
        SettingsFrame.SETTING_MAX_CONCURRENT_STREAMS: 100,
        SettingsFrame.SETTING_INITIAL_WINDOW_SIZE: 65535
    })
    settings_frame = settings.to_frame()

    print(f"Created: {settings_frame}")
    print(f"Packed: {settings_frame.pack().hex()}")

    # 解析
    parsed_frame = HTTP2Frame.unpack(settings_frame.pack())
    print(f"Parsed: {parsed_frame}")

    parsed_settings = SettingsFrame.from_frame(parsed_frame)
    print(parsed_settings)

    # 2. HPACK解码示例
    print("\n2. HPACK Decoding:")
    print("-" * 40)

    decoder = HPACKDecoder()

    # 示例：编码后的头部块（简化）
    # 索引头部（:method: GET）- 使用静态表索引2
    sample_block = bytes([0x82])  # 索引2

    headers = decoder.decode(sample_block)
    print(f"Decoded headers: {headers}")
```

---

## 8. 现代应用

### 8.1 HTTP/2部署现状

#### 8.1.1 浏览器支持

- 所有主流浏览器都支持HTTP/2
- 必须通过TLS部署
- ALPN协商必需

#### 8.1.2 服务器支持

- nginx, Apache, IIS, Caddy等均支持
- 反向代理广泛使用
- CDN普遍支持

### 8.2 HTTP/2与HTTP/3的演进

| 特性 | HTTP/2 | HTTP/3 |
|------|--------|--------|
| 传输层 | TCP | QUIC (UDP) |
| 握手延迟 | 1-RTT (TLS) | 0-RTT |
| 队头阻塞 | TCP层 | 解决 |
| 连接迁移 | 不支持 | 支持 |
| 头部压缩 | HPACK | QPACK |

### 8.3 与后续RFC的关系

| RFC | 主题 | 与RFC 7540关系 |
|-----|------|---------------|
| RFC 7541 | HPACK | 头部压缩规范 |
| RFC 7838 | Alt-Svc | 服务替代指示 |
| RFC 8164 | PRI | HTTP/2优先级 |
| RFC 8336 | ORIGIN | 源框架 |
| RFC 8441 | WebSocket | WebSocket over HTTP/2 |
| RFC 9113 | HTTP/2 | HTTP/2更新规范 |
| RFC 9114 | HTTP/3 | 下一代HTTP |

### 8.4 教学与研究价值

1. **协议优化**: 理解现代协议性能优化技术
2. **二进制协议**: 学习二进制协议设计
3. **压缩算法**: HPACK和QPACK研究
4. **性能评估**: 多路复用性能分析

---

## 参考文献

1. Belshe, M., Peon, R., and M. Thomson. "Hypertext Transfer Protocol Version 2 (HTTP/2)." RFC 7540, May 2015.
2. Peon, R. and H. Ruellan. "HPACK: Header Compression for HTTP/2." RFC 7541, May 2015.
3. Thomson, M. and C. Benfield. "HTTP/2." RFC 9113, June 2022.
4. Bishop, M. "HTTP/3." RFC 9114, June 2022.

---

_文档版本: 1.0_
_最后更新: 2026年_
_状态: 核心RFC映射完成_
