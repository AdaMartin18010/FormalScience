# RFC 5681 - TCP Congestion Control

## 1. RFC概述

### 1.1 基本信息

- **RFC编号**: RFC 5681
- **标题**: TCP Congestion Control
- **发布日期**: 2009年9月
- **状态**: Proposed Standard
- **替代**: RFC 2581
- **更新**: RFC 3390, RFC 6298
- **相关**: RFC 2001, RFC 5682, RFC 8312

### 1.2 历史背景

TCP拥塞控制是互联网稳定运行的基石。RFC 5681标准化了TCP的四种核心拥塞控制算法：慢启动、拥塞避免、快速重传和快速恢复。
这些算法最初由Van Jacobson在1988年提出，经过20多年的实践和改进，最终在此RFC中标准化。

### 1.3 核心贡献

- 标准化TCP拥塞控制算法
- 定义拥塞窗口调整规则
- 规范重传机制
- 确立RTT测量标准

---

## 2. 协议详细说明

### 2.1 拥塞控制目标

#### 2.1.1 设计原则

```
TCP拥塞控制设计目标：

1. 防止网络崩溃
   - 避免注入过多数据导致拥塞
   - 响应网络拥塞信号

2. 公平共享
   - 多个连接公平分享带宽
   - AIMD实现收敛到公平

3. 效率
   - 充分利用可用带宽
   - 最小化空闲时间

4. 响应性
   - 快速检测可用带宽变化
   - 适应网络条件
```

#### 2.1.2 拥塞控制状态

| 状态 | 描述 | cwnd增长 |
|------|------|---------|
| 慢启动 | 探测可用带宽 | 指数增长 |
| 拥塞避免 | 稳定传输 | 线性增长 |
| 快速恢复 | 恢复丢包后传输 | 特殊处理 |

### 2.2 核心算法

#### 2.2.1 慢启动（Slow Start）

```
慢启动算法:

初始化:
  cwnd = 1 * SMSS (或更大，见RFC 3390)
  ssthresh = 较大值 (如 65535)

每收到一个ACK:
  cwnd += min(N, SMSS)  // N是确认的字节数

当 cwnd >= ssthresh:
  进入拥塞避免

当检测到丢包:
  ssthresh = max(cwnd/2, 2*SMSS)
  cwnd = 1 * SMSS  (超时) 或 cwnd = ssthresh (3 dup ACK)
```

#### 2.2.2 拥塞避免（Congestion Avoidance）

```
拥塞避免算法:

每收到一个ACK:
  cwnd += SMSS * SMSS / cwnd  // 每RTT约增加1个SMSS

或等效实现:
  维护一个计数器
  每ACK: count += SMSS
  当 count >= cwnd:
    cwnd += SMSS
    count = 0
```

#### 2.2.3 快速重传（Fast Retransmit）

```
快速重传条件:
- 收到3个重复ACK (dupACK)
- 立即重传丢失的段

处理:
  ssthresh = max(cwnd/2, 2*SMSS)
  cwnd = ssthresh + 3*SMSS  // "inflate"窗口
  重传丢失段
  进入快速恢复
```

#### 2.2.4 快速恢复（Fast Recovery）

```
快速恢复算法:

对每个额外dupACK:
  cwnd += SMSS  // 继续增长窗口

当收到新ACK (确认新数据):
  cwnd = ssthresh  // "deflate"窗口
  退出快速恢复
  进入拥塞避免

当超时:
  ssthresh = max(cwnd/2, 2*SMSS)
  cwnd = 1 * SMSS
  进入慢启动
```

### 2.3 拥塞窗口动态

```
cwnd随时间变化:

高
|                    ____ 拥塞避免
|               ____/
|          ____/
|     ____/
|____/          丢包
|    \\         /\\
|     \\       /  \\
|      \\_____/    \\____
|       快速恢复    慢启动
|
+----------------------------> 时间

慢启动: 指数增长
拥塞避免: 线性增长
丢包后: 快速恢复或慢启动
```

---

## 3. 关键参数

### 3.1 变量定义

| 变量 | 全称 | 描述 | 初始值 |
|------|------|------|--------|
| cwnd | Congestion Window | 拥塞窗口 | 2-4 * SMSS |
| ssthresh | Slow Start Threshold | 慢启动阈值 | 65535 |
| rwnd | Receiver Window | 接收窗口 | 从ACK获得 |
| SMSS | Sender MSS | 发送方最大段大小 | 协商确定 |
| RMSS | Receiver MSS | 接收方最大段大小 | 协商确定 |
| FlightSize | - | 在途数据量 | 动态 |

### 3.2 发送窗口

```
实际发送窗口 = min(cwnd, rwnd)

限制因素:
- cwnd: 网络容量限制（拥塞控制）
- rwnd: 接收方缓冲区限制（流量控制）
```

### 3.3 RTT测量

```
平滑RTT计算 (RFC 6298):

Initial:
  SRTT = R  (第一个RTT样本)
  RTTVAR = R / 2
  RTO = SRTT + max(G, K * RTTVAR)  // K = 4

后续更新:
  RTTVAR = (1 - beta) * RTTVAR + beta * |SRTT - R'|
  SRTT = (1 - alpha) * SRTT + alpha * R'
  RTO = SRTT + max(G, K * RTTVAR)

其中:
  alpha = 1/8
  beta = 1/4
  G = 时钟粒度
  K = 4

RTO边界:
  RTO >= 1秒 (初始)
  RTO >= 200ms (最小值)
```

---

## 4. 状态机

### 4.1 TCP拥塞控制状态机

```
                    +------------------+
                    |      OPEN        |
                    |  (Initial state) |
                    +--------+---------+
                             |
                             v
                    +--------+---------+
                    |   SLOW START     |
                    |  cwnd < ssthresh |
                    +--------+---------+
                             |
         +-------------------+-------------------+
         |                                       |
    cwnd >= ssthresh                         Timeout
         |                                       |
         v                                       v
+--------+---------+                   +----------+----------+
| CONGESTION       |                   |   SLOW START (reset)|
| AVOIDANCE        |                   |   cwnd = 1*SMSS     |
| cwnd += SMSS     |                   |   ssthresh =        |
| per RTT          |                   |     max(Flight/2,2) |
+--------+---------+                   +----------+----------+
         |                                       |
         |                                       |
         | 3 dup ACK                            |
         v                                       |
+--------+---------+                             |
| FAST RETRANSMIT  |                             |
| Retransmit       |                             |
| lost segment     |                             |
+--------+---------+                             |
         |                                       |
         v                                       |
+--------+---------+                             |
| FAST RECOVERY    |<----------------------------+
| cwnd = ssthresh  |
| + 3*SMSS         |
+--------+---------+
         |
         | New ACK
         v
+--------+---------+
| CONGESTION       |
| AVOIDANCE        |
| (continue)       |
+------------------+
```

### 4.2 丢包处理决策

```
                    +------------------+
                    |  Loss Detected   |
                    +--------+---------+
                             |
              +--------------+--------------+
              |                             |
        3 dup ACKs                     Timeout
              |                             |
              v                             v
    +---------+---------+      +----------+----------+
    | FAST RECOVERY     |      |  SLOW START         |
    | ssthresh =        |      |  ssthresh =         |
    |   max(Flight/2,   |      |    max(Flight/2,    |
    |   2*SMSS)         |      |    2*SMSS)          |
    | cwnd = ssthresh   |      |  cwnd = 1*SMSS      |
    | + 3*SMSS          |      |  (retransmit)       |
    +---------+---------+      +----------+----------+
              |                             |
              v                             v
    +---------+---------+      +----------+----------+
    | Partial ACK?      |      |  Continue           |
    | (recov > SND.UNA) |      |  slow start         |
    +---------+---------+      |  until ssthresh     |
         | Yes          | No   +---------------------+
         v              v
    +----+-----+  +-----+------+
    |Retransmit|  | New ACK    |
    |next lost |  | (Flight >= |-> Continue fast
    |segment   |  |  cwnd)?    |   recovery
    +----+-----+  +-----+------+
         |              |
         |              | Yes
         +------+-------+
                |
                v
         +------+-------+
         | Exit fast    |
         | recovery     |
         | cwnd =       |
         |  ssthresh    |
         +--------------+
```

---

## 5. 安全性考虑

### 5.1 拥塞控制攻击

#### 5.1.1 ACK分裂攻击

- **攻击方式**: 接收方发送多个ACK确认同一数据
- **影响**: 发送方cwnd增长过快
- **缓解措施**:
  - 限制每个数据段的ACK增长
  - 字节计数而非包计数

#### 5.1.2 乐观ACK攻击

- **攻击方式**: 接收方提前确认未接收数据
- **影响**: 发送方加速发送，导致拥塞
- **缓解措施**:
  - 拥塞窗口上限
  - 检测异常ACK模式

#### 5.1.3 虚假丢包攻击

- **攻击方式**: 中间人伪造丢包信号
- **影响**: 降低连接吞吐量
- **缓解措施**:
  - 拥塞响应限制
  - 异常检测

### 5.2 安全建议

```
拥塞控制安全最佳实践:

1. ACK验证
   - 验证ACK号单调递增
   - 限制ACK增长速率

2. 速率限制
   - 最大cwnd限制
   - 最小RTO限制

3. 拥塞响应
   - 限制拥塞窗口减少频率
   - 检测异常拥塞信号

4. 测量保护
   - RTT样本验证
   - 异常值过滤
```

---

## 6. 与教材对标的章节

### 6.1 《计算机网络：自顶向下方法》

| RFC 5681内容 | 对应章节 |
|-------------|----------|
| 拥塞控制概述 | 第3章：运输层 - 3.6 拥塞控制原理 |
| 慢启动 | 3.6.1 慢启动 |
| 拥塞避免 | 3.6.2 拥塞避免 |
| 快速恢复 | 3.6.3 快速恢复 |
| TCP吞吐量 | 3.7.1 公平性 |

### 6.2 《TCP/IP详解 卷1：协议》

| RFC 5681内容 | 对应章节 |
|-------------|----------|
| 拥塞控制 | 第21章：TCP超时与重传 |
| 慢启动 | 21.5 拥塞示例 |
| 拥塞避免 | 21.6 拥塞避免 |
| 快速重传 | 21.7 快速重传和快速恢复 |

### 6.3 《计算机网络》（谢希仁）

| RFC 5681内容 | 对应章节 |
|-------------|----------|
| TCP拥塞控制 | 第5章：运输层 - 5.8 TCP的拥塞控制 |
| 慢开始 | 5.8.1 慢开始 |
| 拥塞避免 | 5.8.2 拥塞避免 |
| 快重传 | 5.8.3 快重传 |
| 快恢复 | 5.8.4 快恢复 |

---

## 7. 实现示例

### 7.1 Python实现：RFC 5681拥塞控制

```python
import time
from dataclasses import dataclass, field
from typing import Optional, List
from enum import Enum

class CongestionState(Enum):
    """拥塞控制状态"""
    SLOW_START = "slow_start"
    CONGESTION_AVOIDANCE = "congestion_avoidance"
    FAST_RECOVERY = "fast_recovery"

@dataclass
class TCPCongestionControl:
    """RFC 5681 TCP拥塞控制实现"""

    # 常量
    SMSS: int = 1460  # 发送方最大段大小
    INITIAL_CWND: int = field(default=2)  # 初始拥塞窗口（以SMSS计）

    # 拥塞控制变量
    cwnd: float = field(default=0)  # 拥塞窗口（字节）
    ssthresh: float = field(default=65535)  # 慢启动阈值（字节）
    state: CongestionState = field(default=CongestionState.SLOW_START)

    # 统计
    packets_sent: int = 0
    packets_acked: int = 0
    packets_retransmitted: int = 0
    dup_ack_count: int = 0
    last_ack_num: int = -1

    # 快速恢复状态
    recover: int = 0  # 恢复点

    def __post_init__(self):
        self.cwnd = self.INITIAL_CWND * self.SMSS
        print(f"[CC] Initialized: cwnd={self.cwnd}, ssthresh={self.ssthresh}")

    def on_ack_received(self, ack_num: int, bytes_acked: int,
                       flight_size: int) -> dict:
        """
        处理ACK到达

        Args:
            ack_num: 确认号
            bytes_acked: 确认的字节数
            flight_size: 在途数据量

        Returns:
            操作结果字典
        """
        result = {'action': 'none', 'cwnd_before': self.cwnd}

        # 检查重复ACK
        if ack_num == self.last_ack_num:
            self.dup_ack_count += 1
            print(f"[CC] Dup ACK #{self.dup_ack_count} for seq={ack_num}")

            if self.state == CongestionState.FAST_RECOVERY:
                # 快速恢复中，继续增长窗口
                self.cwnd += self.SMSS
                result['action'] = 'inflate_cwnd'

            elif self.dup_ack_count == 3:
                # 第3个重复ACK，触发快速重传
                result.update(self._fast_retransmit(flight_size))

        else:
            # 新ACK
            self.dup_ack_count = 0
            self.last_ack_num = ack_num

            if self.state == CongestionState.FAST_RECOVERY:
                # 检查是否完全恢复
                if ack_num >= self.recover:
                    self._exit_fast_recovery()
                    result['action'] = 'exit_fast_recovery'
                else:
                    # 部分ACK，重传下一个丢失段
                    result['action'] = 'partial_ack_retransmit'

            elif self.state == CongestionState.SLOW_START:
                # 慢启动：指数增长
                self.cwnd += bytes_acked
                result['action'] = 'slow_start_growth'

                # 检查是否达到阈值
                if self.cwnd >= self.ssthresh:
                    self.state = CongestionState.CONGESTION_AVOIDANCE
                    print(f"[CC] Entering Congestion Avoidance: cwnd={self.cwnd:.0f}")

            elif self.state == CongestionState.CONGESTION_AVOIDANCE:
                # 拥塞避免：线性增长
                # RFC 5681: cwnd += SMSS * SMSS / cwnd per ACK
                increment = self.SMSS * bytes_acked / self.cwnd
                self.cwnd += increment
                result['action'] = 'congestion_avoidance_growth'

            self.packets_acked += 1

        result['cwnd_after'] = self.cwnd
        result['state'] = self.state.value
        return result

    def _fast_retransmit(self, flight_size: int) -> dict:
        """快速重传处理"""
        print(f"[CC] Fast Retransmit triggered!")

        # 记录恢复点
        self.recover = flight_size + self.last_ack_num

        # 调整ssthresh和cwnd
        self.ssthresh = max(flight_size // 2, 2 * self.SMSS)
        self.cwnd = self.ssthresh + 3 * self.SMSS

        self.state = CongestionState.FAST_RECOVERY
        self.packets_retransmitted += 1

        print(f"  ssthresh={self.ssthresh:.0f}, cwnd={self.cwnd:.0f}")

        return {
            'action': 'fast_retransmit',
            'retransmit_seq': self.last_ack_num,
            'ssthresh': self.ssthresh,
            'recover': self.recover
        }

    def _exit_fast_recovery(self):
        """退出快速恢复"""
        print(f"[CC] Exiting Fast Recovery")
        self.cwnd = self.ssthresh
        self.state = CongestionState.CONGESTION_AVOIDANCE
        self.dup_ack_count = 0
        print(f"  cwnd reset to ssthresh={self.cwnd:.0f}")

    def on_timeout(self, flight_size: int) -> dict:
        """超时处理"""
        print(f"[CC] Timeout occurred!")

        # RFC 5681: 超时后重新慢启动
        self.ssthresh = max(flight_size // 2, 2 * self.SMSS)
        self.cwnd = self.INITIAL_CWND * self.SMSS
        self.state = CongestionState.SLOW_START
        self.dup_ack_count = 0

        print(f"  ssthresh={self.ssthresh:.0f}, cwnd reset to {self.cwnd}")

        return {
            'action': 'timeout_reset',
            'ssthresh': self.ssthresh,
            'cwnd': self.cwnd,
            'state': self.state.value
        }

    def can_send(self, flight_size: int, rwnd: int) -> bool:
        """检查是否可以发送新数据"""
        # 受限于cwnd和rwnd
        return flight_size < min(int(self.cwnd), rwnd)

    def get_send_window(self, rwnd: int) -> int:
        """获取当前发送窗口"""
        return int(min(self.cwnd, rwnd))

    def get_stats(self) -> dict:
        """获取统计信息"""
        return {
            'state': self.state.value,
            'cwnd': self.cwnd,
            'ssthresh': self.ssthresh,
            'packets_sent': self.packets_sent,
            'packets_acked': self.packets_acked,
            'packets_retransmitted': self.packets_retransmitted
        }

    def __str__(self) -> str:
        return (f"CC[state={self.state.value}, "
                f"cwnd={self.cwnd:.1f}, ssthresh={self.ssthresh:.1f}]")


@dataclass
class RTTMeasurement:
    """RTT测量（RFC 6298）"""

    # 平滑因子
    ALPHA: float = 0.125  # 1/8
    BETA: float = 0.25    # 1/4
    K: int = 4

    srtt: Optional[float] = None  # 平滑RTT
    rttvar: Optional[float] = None  # RTT方差
    rto: float = 1.0  # 重传超时（秒）

    # 边界
    MIN_RTO: float = 0.2  # 200ms
    MAX_RTO: float = 60.0  # 60s

    def update(self, measured_rtt: float):
        """更新RTT估计"""
        if self.srtt is None:
            # 第一个样本
            self.srtt = measured_rtt
            self.rttvar = measured_rtt / 2
        else:
            # 后续样本
            self.rttvar = (1 - self.BETA) * self.rttvar + \
                         self.BETA * abs(self.srtt - measured_rtt)
            self.srtt = (1 - self.ALPHA) * self.srtt + \
                       self.ALPHA * measured_rtt

        # 计算RTO
        self.rto = self.srtt + max(0.01, self.K * self.rttvar)

        # 边界检查
        self.rto = max(self.MIN_RTO, min(self.MAX_RTO, self.rto))

        print(f"[RTT] measured={measured_rtt:.3f}s, SRTT={self.srtt:.3f}s, "
              f"RTTVAR={self.rttvar:.3f}s, RTO={self.rto:.3f}s")

    def backoff(self):
        """RTO指数退避"""
        self.rto = min(self.MAX_RTO, self.rto * 2)
        print(f"[RTT] RTO backed off to {self.rto:.3f}s")


# 使用示例
if __name__ == "__main__":
    print("=" * 60)
    print("RFC 5681 TCP Congestion Control Demo")
    print("=" * 60)

    # 1. 慢启动演示
    print("\n1. Slow Start Phase:")
    print("-" * 40)

    cc = TCPCongestionControl(SMSS=1000, INITIAL_CWND=2)
    rtt = RTTMeasurement()

    flight_size = 0
    rwnd = 100000  # 大接收窗口

    # 模拟发送和ACK
    for i in range(10):
        # 发送数据
        while cc.can_send(flight_size, rwnd):
            print(f"  Send: cwnd={cc.cwnd:.0f}, flight={flight_size}")
            flight_size += cc.SMSS
            cc.packets_sent += 1

        # 模拟ACK到达（RTT=0.1s）
        time.sleep(0.01)
        ack_bytes = min(flight_size, int(cc.cwnd))
        result = cc.on_ack_received(ack_num=i*1000, bytes_acked=ack_bytes,
                                    flight_size=flight_size)
        flight_size -= ack_bytes

        rtt.update(0.1)

        if i == 5:  # 达到ssthresh
            print(f"\n  State: {cc.state.value}, cwnd growth slowing...")

    # 2. 快速重传演示
    print("\n2. Fast Retransmit and Recovery:")
    print("-" * 40)

    # 重置
    cc = TCPCongestionControl(SMSS=1000, INITIAL_CWND=2)
    cc.cwnd = 10000  # 当前cwnd
    cc.ssthresh = 20000
    cc.state = CongestionState.CONGESTION_AVOIDANCE
    flight_size = 8000

    print(f"Initial: {cc}, flight_size={flight_size}")

    # 模拟3个重复ACK
    for i in range(5):
        result = cc.on_ack_received(ack_num=1000, bytes_acked=0,
                                    flight_size=flight_size)
        print(f"  Dup ACK {i+1}: {result.get('action', 'none')}")

        if result['action'] == 'fast_retransmit':
            break

    # 模拟恢复ACK
    print("\n  Recovery ACKs:")
    for i in range(3):
        result = cc.on_ack_received(ack_num=2000 + i*1000, bytes_acked=1000,
                                    flight_size=flight_size)
        print(f"    ACK {i+1}: {result.get('action', 'none')}, state={cc.state.value}")
        if result['action'] == 'exit_fast_recovery':
            break

    # 3. 超时演示
    print("\n3. Timeout Recovery:")
    print("-" * 40)

    cc = TCPCongestionControl(SMSS=1000, INITIAL_CWND=2)
    cc.cwnd = 20000
    cc.ssthresh = 20000
    cc.state = CongestionState.CONGESTION_AVOIDANCE
    flight_size = 15000

    print(f"Before timeout: {cc}")
    result = cc.on_timeout(flight_size)
    print(f"After timeout: {cc}")

    # 4. 统计
    print("\n4. Final Statistics:")
    print("-" * 40)
    stats = cc.get_stats()
    for key, value in stats.items():
        print(f"  {key}: {value}")
```

---

## 8. 现代应用

### 8.1 拥塞控制演进

#### 8.1.1 现代算法

| 算法 | 特点 | RFC |
|------|------|-----|
| CUBIC | Linux默认，高速网络优化 | 8312 |
| BBR | Google开发，基于模型 | - |
| Vegas | 基于延迟的拥塞控制 | - |
| DCTCP | 数据中心TCP | - |

#### 8.1.2 多路径TCP

- MPTCP拥塞控制
- 子流间协调
- 共享拥塞窗口

### 8.2 与相关RFC的关系

| RFC | 主题 | 与RFC 5681关系 |
|-----|------|---------------|
| RFC 2581 | TCP拥塞控制（旧） | 被5681替代 |
| RFC 3390 | 初始窗口 | 更新初始cwnd |
| RFC 5682 | F-RTO | 假超时恢复 |
| RFC 6298 | RTO计算 | 更新RTT/RTO算法 |
| RFC 8312 | CUBIC | 现代拥塞控制 |
| RFC 9002 | QUIC CC | QUIC拥塞控制 |

### 8.3 教学与研究价值

1. **经典算法**: 理解拥塞控制基础
2. **网络稳定性**: 理解AIMD的收敛性
3. **性能分析**: 吞吐量、延迟分析
4. **现代改进**: 对比新旧算法

---

## 参考文献

1. Allman, M., Paxson, V., and E. Blanton. "TCP Congestion Control." RFC 5681, September 2009.
2. Ha, S., Rhee, I., and L. Xu. "CUBIC for Fast Long-Distance Networks." RFC 8312, February 2018.
3. Paxson, V., et al. "Computing TCP's Retransmission Timer." RFC 6298, June 2011.
4. Floyd, S. "Congestion Control Principles." RFC 2914, September 2000.

---

_文档版本: 1.0_
_最后更新: 2026年_
_状态: 核心RFC映射完成_
