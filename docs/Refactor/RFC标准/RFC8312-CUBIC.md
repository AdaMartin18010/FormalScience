# RFC 8312 - CUBIC for Fast Long-Distance Networks

## 1. RFC概述

### 1.1 基本信息

- **RFC编号**: RFC 8312
- **标题**: CUBIC for Fast Long-Distance Networks
- **发布日期**: 2018年2月
- **状态**: Informational
- **作者**: Ha, S., Rhee, I., Xu, L.
- **相关**: RFC 5681, RFC 9002 (QUIC CUBIC)

### 1.2 历史背景

传统TCP拥塞控制（Reno）在高带宽延迟积（BDP）网络中性能不佳：

- 慢启动后期窗口增长过慢
- 拥塞避免线性增长需要极长时间恢复
- 多个流不能快速收敛到公平

CUBIC在2008年开发，2018年成为RFC，现为Linux默认拥塞控制算法。

### 1.3 核心贡献

- 提出三次方窗口增长函数
- 在BDP网络实现高可扩展性
- 保持Reno流之间的公平性
- 提供TCP友好性保证

---

## 2. 协议详细说明

### 2.1 CUBIC设计原理

#### 2.1.1 核心思想

```
CUBIC窗口增长函数:

W(t) = C * (t - K)^3 + W_max

其中:
- W(t): t时刻的窗口大小
- C: CUBIC缩放因子（常数）
- t: 上次丢包后的时间
- K: W增长到W_max所需时间
- W_max: 上次丢包前的窗口大小

K = cubic_root(W_max * (1 - β) / C)

β: 乘法减少因子（通常0.7）
```

#### 2.1.2 增长曲线

```
窗口
  ^
  |         W_max ___________  平台期（保守）
  |              /|            |
  |             / |            |
  |            /  |            |
  |           /   |            |
  |          /    |            |  凸增长（探测）
  |         /     |            |
  |        /      |            |
  |_______/       |            |
  |    凹增长     |            |
  |   （稳定）    |            |
  +--------------------------------> 时间
      |           |
      |<--- K --->|
      |
     丢包

区域1 (t < K): 凹增长 - 快速恢复带宽
区域2 (t = K): 平台期 - 保守探测
区域3 (t > K): 凸增长 - 继续探测可用带宽
```

### 2.2 CUBIC算法

#### 2.2.1 窗口计算

```
CUBIC算法伪代码:

每当ACK到达:
    if (t < K):
        // 凹增长区域
        W_cubic = C * (K - t)^3 + W_max
    else if (t == K):
        // 平台期
        W_cubic = W_max
    else:
        // 凸增长区域
        W_cubic = C * (t - K)^3 + W_max

    // TCP友好性计算
    W_tcp = W_max * β + 3 * (1 - β) / (1 + β) * t / RTT

    // 最终窗口
    if (W_cubic < W_tcp && t < K):
        cwnd = W_tcp
    else:
        cwnd = W_cubic

    t += RTT

当检测到丢包:
    W_max = cwnd
    ssthresh = cwnd * β
    cwnd = ssthresh
    t = 0
    K = cubic_root(W_max * (1 - β) / C)
```

#### 2.2.2 关键参数

| 参数 | 默认值 | 描述 |
|------|--------|------|
| C | 0.4 | CUBIC缩放因子 |
| β | 0.7 | 乘法减少因子 |
| α | - | Reno风格增长（TCP友好模式） |

### 2.3 TCP友好性

#### 2.3.1 友好性保证

```
CUBIC与Reno共存:

网络带宽
  ^
  |                    CUBIC流
  |                  /
  |                /
  |              /
  |    Reno流  /
  |          /
  |        /
  |      /
  |____/
  |
  +-------------------------> 时间

- 短RTT网络: CUBIC退化为Reno行为
- 长RTT网络: CUBIC获得更高吞吐
- 长期共存: 收敛到公平
```

#### 2.3.2 友好性模式

```
当 W_cubic < W_tcp:
    使用 W_tcp (Reno风格增长)

当 W_cubic >= W_tcp:
    使用 W_cubic (CUBIC增长)

这确保在低速网络中:
- CUBIC不会抢占Reno带宽
- 保持向后兼容
```

---

## 3. 数学分析

### 3.1 三次方函数详解

```
CUBIC窗口函数: W(t) = C * (t - K)^3 + W_max

特性分析:
1. 在 t = K 处取得最小值 W_max
2. 导数: dW/dt = 3C * (t - K)^2
   - t < K: 导数递减（凹函数）
   - t > K: 导数递增（凸函数）
3. 对称性: 关于点 (K, W_max) 中心对称

参数C的影响:
- C越大: 窗口增长越快，越激进
- C越小: 窗口增长越慢，越保守
- 默认值0.4平衡性能和稳定性
```

### 3.2 收敛性分析

```
CUBIC收敛到公平:

假设两个CUBIC流竞争带宽B:

时间t足够大时:
  W1(t) ≈ C * (t - K1)^3 + W1_max
  W2(t) ≈ C * (t - K2)^3 + W2_max

在平衡状态:
  W1(t) + W2(t) = B * RTT

CUBIC的特性使得:
- 窗口大的流增长更慢
- 窗口小的流增长更快
- 最终收敛到 W1 ≈ W2
```

### 3.3 与Reno对比

| 特性 | Reno | CUBIC |
|------|------|-------|
| 增长方式 | 线性 | 三次方 |
| BDP适应性 | 差 | 好 |
| 收敛速度 | 慢 | 快 |
| RTT公平性 | 偏好短RTT | 更公平 |
| 稳定性 | 抖动大 | 平稳 |

---

## 4. 状态机

### 4.1 CUBIC状态机

```
                    +------------------+
                    |      START       |
                    +--------+---------+
                             |
                             v
                    +--------+---------+
                    |   MAX PROBING    |
                    |  (t < K)         |
                    |  W(t) < W_max    |
                    |  凹增长           |
                    +--------+---------+
                             |
                             | W(t) >= W_max
                             v
                    +--------+---------+
                    |    SADDLE POINT  |
                    |    (t ≈ K)       |
                    |    W(t) ≈ W_max  |
                    +--------+---------+
                             |
                             | t > K
                             v
                    +--------+---------+
                    |   PROBING        |
                    |   (t > K)        |
                    |   W(t) > W_max   |
                    |   凸增长          |
                    +--------+---------+
                             |
                             | Packet loss
                             v
                    +--------+---------+
                    |   MULT. DECREASE |
                    |   W_max = W      |
                    |   W = β * W      |
                    |   t = 0          |
                    |   Recalculate K  |
                    +--------+---------+
                             |
                             v
                    +--------+---------+
                    |   MAX PROBING    |<----+
                    +------------------+     |
                             |               |
                             +---------------+
```

### 4.2 与标准TCP状态集成

```
                    +------------------+
                    |   CUBIC ACTIVE   |
                    +--------+---------+
                             |
              +--------------+--------------+
              |                             |
         cwnd < ssthresh               cwnd >= ssthresh
              |                             |
              v                             v
    +---------+---------+      +----------+----------+
    |   TCP MODE        |      |   CUBIC MODE        |
    |   (Slow Start)    |      |   (Congestion       |
    |   Use standard    |      |    Avoidance)       |
    |   slow start      |      |   Use CUBIC         |
    +---------+---------+      |   window function   |
              |                +----------+----------+
              |                             |
              +--------------+--------------+
                             |
                             v
                    +--------+---------+
                    |   Loss Detected  |
                    +--------+---------+
                             |
              +--------------+--------------+
              |                             |
         3 dup ACK                      Timeout
              |                             |
              v                             v
    +---------+---------+      +----------+----------+
    | Fast Recovery     |      |   Slow Start        |
    | (Reno style)      |      |   Reset             |
    | Recalculate       |      |   ssthresh = β*W    |
    | W_max, K          |      |   cwnd = 1*MSS      |
    +-------------------+      +---------------------+
```

---

## 5. 安全性考虑

### 5.1 CUBIC安全特性

#### 5.1.1 RTT公平性

```
CUBIC改进RTT公平性:

Reno的问题:
- 短RTT流增长更快
- 长RTT流被饿死

CUBIC的解决:
- 增长基于实际时间，非RTT
- 长RTT流有更好的增长机会
- 更公平的带宽分配

数学基础:
  Reno: cwnd增长 ∝ 1/RTT
  CUBIC: cwnd增长 ∝ t (实际时间)
```

#### 5.1.2 稳定性

```
CUBIC稳定性保证:

1. 窗口增长上界
   - 三次方增长有自然限制
   - 不会无限快速增长

2. 丢包响应
   - 保守的乘法减少（β=0.7）
   - 比Reno更平稳

3. 带宽探测
   - 平台期防止过度激进
   - 快速恢复后平稳增长
```

### 5.2 部署考虑

```
CUBIC部署最佳实践:

1. 参数调优
   - C值：0.3-0.5（默认0.4）
   - β值：0.6-0.8（默认0.7）

2. 缓冲区大小
   - BDP = bandwidth * RTT
   - 缓冲区 >= BDP

3. 与AQM配合
   - ECN支持（RFC 3168）
   - RED/Codel参数调优

4. 多流公平性
   - 同一主机多流公平
   - 与Reno流共存
```

---

## 6. 与教材对标的章节

### 6.1 《计算机网络：自顶向下方法》

| RFC 8312内容 | 对应章节 |
|-------------|----------|
| CUBIC概述 | 第3章：运输层 - 3.7 TCP拥塞控制（扩展） |
| 高速网络 | 3.7 现代拥塞控制算法 |
| 算法对比 | 课后扩展阅读 |

### 6.2 《TCP/IP详解》系列

| RFC 8312内容 | 对应章节 |
|-------------|----------|
| 拥塞控制演进 | 第24章：TCP未来和性能 |
| CUBIC算法 | 现代TCP实现补充 |

### 6.3 研究论文

| RFC 8312内容 | 参考 |
|-------------|------|
| CUBIC原始论文 | Ha et al., "CUBIC: A New TCP-Friendly High-Speed TCP Variant" |
| Linux实现 | tcp_cubic.c in Linux kernel |

---

## 7. 实现示例

### 7.1 Python实现：CUBIC算法

```python
import time
import math
from dataclasses import dataclass, field
from typing import Optional

@dataclass
class CUBIC:
    """CUBIC拥塞控制实现（RFC 8312）"""

    # CUBIC参数
    C: float = 0.4           # 缩放因子
    beta: float = 0.7        # 乘法减少因子

    # 状态变量
    cwnd: float = field(default=10.0)  # 当前拥塞窗口
    ssthresh: float = field(default=65535.0)

    # CUBIC特定状态
    W_max: float = 0.0       # 上次丢包前窗口
    K: float = 0.0           # 到达W_max的时间
    epoch_start: float = 0.0 # 纪元开始时间
    origin_point: float = 0.0 # 原点

    # RTT估计
    srtt: float = 0.1        # 平滑RTT（秒）

    # 统计
    packets_sent: int = 0
    packets_acked: int = 0
    loss_events: int = 0

    # 常量
    SMSS: int = 1460         # 段大小

    def __post_init__(self):
        self.epoch_start = time.time()
        self.origin_point = self.cwnd
        self.W_max = self.cwnd
        print(f"[CUBIC] Initialized: C={self.C}, β={self.beta}, cwnd={self.cwnd}")

    def _cubic_root(self, x: float) -> float:
        """计算立方根"""
        return math.copysign(abs(x) ** (1/3), x)

    def _cubic_function(self, t: float) -> float:
        """
        CUBIC窗口增长函数: W(t) = C * (t - K)^3 + W_max

        Args:
            t: 上次丢包后的时间

        Returns:
            计算得到的窗口大小
        """
        return self.C * (t - self.K) ** 3 + self.W_max

    def _tcp_friendly_window(self, t: float) -> float:
        """
        TCP友好窗口计算
        W_tcp(t) = W_max * β + 3 * (1-β) / (1+β) * t / RTT
        """
        return self.W_max * self.beta + \
               3 * (1 - self.beta) / (1 + self.beta) * t / self.srtt

    def on_ack_received(self, bytes_acked: int, flight_size: int) -> dict:
        """
        处理ACK到达

        Returns:
            操作结果
        """
        result = {'cwnd_before': self.cwnd}

        # 计算时间t
        t = time.time() - self.epoch_start

        # 计算目标窗口
        W_cubic = self._cubic_function(t)
        W_tcp = self._tcp_friendly_window(t)

        # TCP友好性选择
        if W_cubic < W_tcp and t < self.K:
            # 使用TCP友好窗口
            target = W_tcp
            mode = "tcp_friendly"
        else:
            # 使用CUBIC窗口
            target = W_cubic
            mode = "cubic"

        # 确保窗口不会小于0
        target = max(target, 1.0)

        # 更新窗口
        self.cwnd = target

        self.packets_acked += 1

        result.update({
            'cwnd_after': self.cwnd,
            't': t,
            'K': self.K,
            'W_cubic': W_cubic,
            'W_tcp': W_tcp,
            'mode': mode
        })

        return result

    def on_loss_detected(self, flight_size: int) -> dict:
        """
        处理丢包

        根据RFC 8312:
        - W_max = cwnd
        - ssthresh = cwnd * β
        - cwnd = ssthresh
        - Recalculate K
        """
        print(f"[CUBIC] Loss detected: cwnd={self.cwnd:.1f}")

        self.loss_events += 1

        # 记录W_max
        self.W_max = self.cwnd

        # 乘法减少
        self.ssthresh = max(self.cwnd * self.beta, 2 * self.SMSS)
        self.cwnd = self.ssthresh

        # 重新开始CUBIC纪元
        self.epoch_start = time.time()
        self.origin_point = self.cwnd

        # 重新计算K
        self.K = self._cubic_root(self.W_max * (1 - self.beta) / self.C)

        print(f"  W_max={self.W_max:.1f}, ssthresh={self.ssthresh:.1f}")
        print(f"  New cwnd={self.cwnd:.1f}, K={self.K:.3f}s")

        return {
            'W_max': self.W_max,
            'ssthresh': self.ssthresh,
            'cwnd': self.cwnd,
            'K': self.K
        }

    def can_send(self, flight_size: int, rwnd: int) -> bool:
        """检查是否可以发送"""
        return flight_size < min(int(self.cwnd), rwnd)

    def get_stats(self) -> dict:
        """获取统计"""
        return {
            'cwnd': self.cwnd,
            'ssthresh': self.ssthresh,
            'W_max': self.W_max,
            'K': self.K,
            'C': self.C,
            'beta': self.beta,
            'loss_events': self.loss_events
        }

    def __str__(self) -> str:
        return (f"CUBIC[cwnd={self.cwnd:.1f}, W_max={self.W_max:.1f}, "
                f"K={self.K:.3f}, losses={self.loss_events}]")


class CUBICSimulator:
    """CUBIC行为模拟器"""

    def __init__(self, rtt: float = 0.1):
        self.cubic = CUBIC()
        self.cubic.srtt = rtt
        self.flight_size = 0
        self.rwnd = 1000000  # 大接收窗口
        self.time_step = rtt / 10  # 模拟粒度
        self.current_time = 0.0
        self.history = []

    def simulate(self, duration: float, loss_times: list = None):
        """
        模拟CUBIC行为

        Args:
            duration: 模拟时长（秒）
            loss_times: 丢包时间点列表
        """
        if loss_times is None:
            loss_times = []

        print(f"\n[CUBIC Simulation] RTT={self.cubic.srtt}s, duration={duration}s")
        print("-" * 60)

        loss_idx = 0

        while self.current_time < duration:
            # 检查丢包
            if loss_idx < len(loss_times) and self.current_time >= loss_times[loss_idx]:
                print(f"\n[Time {self.current_time:.2f}s] Loss event!")
                self.cubic.on_loss_detected(self.flight_size)
                loss_idx += 1

            # 发送数据
            packets_sent = 0
            while self.cubic.can_send(self.flight_size, self.rwnd):
                self.flight_size += self.cubic.SMSS
                packets_sent += 1
                self.cubic.packets_sent += 1

            # 模拟ACK（简化：假设全部确认）
            if self.flight_size > 0:
                acked = min(self.flight_size, int(self.cubic.cwnd))
                result = self.cubic.on_ack_received(acked, self.flight_size)
                self.flight_size -= acked

            # 记录状态
            self.history.append({
                'time': self.current_time,
                'cwnd': self.cubic.cwnd,
                'mode': result.get('mode', 'unknown'),
                'flight': self.flight_size
            })

            # 每0.5秒输出一次
            if int(self.current_time * 2) != int((self.current_time - self.time_step) * 2):
                print(f"  t={self.current_time:.2f}s: cwnd={self.cubic.cwnd:.1f}, "
                      f"mode={result.get('mode', '-')}, flight={self.flight_size}")

            self.current_time += self.time_step

        print(f"\nSimulation complete. Final: {self.cubic}")

    def analyze(self):
        """分析模拟结果"""
        if not self.history:
            return

        cwnds = [h['cwnd'] for h in self.history]
        print(f"\n[CUBIC Analysis]")
        print(f"  Max cwnd: {max(cwnds):.1f}")
        print(f"  Min cwnd: {min(cwnds):.1f}")
        print(f"  Avg cwnd: {sum(cwnds)/len(cwnds):.1f}")
        print(f"  Final cwnd: {cwnds[-1]:.1f}")


# 使用示例
if __name__ == "__main__":
    print("=" * 60)
    print("RFC 8312 CUBIC Congestion Control Demo")
    print("=" * 60)

    # 1. 基础CUBIC行为
    print("\n1. Basic CUBIC Growth:")
    print("-" * 40)

    sim = CUBICSimulator(rtt=0.1)
    sim.simulate(duration=3.0, loss_times=[1.5])
    sim.analyze()

    # 2. 参数影响
    print("\n2. Parameter Impact (C value):")
    print("-" * 40)

    for C in [0.2, 0.4, 0.8]:
        print(f"\nC = {C}:")
        cubic = CUBIC(C=C, cwnd=1000)
        cubic.W_max = 1000
        cubic.K = cubic._cubic_root(cubic.W_max * (1 - cubic.beta) / cubic.C)

        # 计算不同时间的窗口
        for t in [0.5, 1.0, 2.0, 3.0]:
            W = cubic._cubic_function(t)
            print(f"  t={t}s: W={W:.1f}")

    # 3. 与Reno对比
    print("\n3. Comparison with Reno-style growth:")
    print("-" * 40)

    cubic = CUBIC(cwnd=1000)
    cubic.W_max = 1000
    cubic.srtt = 0.1
    cubic.K = cubic._cubic_root(cubic.W_max * (1 - cubic.beta) / cubic.C)

    print(f"Initial: W_max={cubic.W_max}, K={cubic.K:.3f}s")
    print(f"{'Time':<10} {'CUBIC':<15} {'TCP-Friendly':<15} {'Reno':<15}")
    print("-" * 55)

    for t in [0.1, 0.5, 1.0, 2.0, 3.0, 5.0]:
        W_cubic = cubic._cubic_function(t)
        W_tcp = cubic._tcp_friendly_window(t)

        # Reno增长: W = W_max * β + α * t / RTT, α ≈ 1
        W_reno = cubic.W_max * cubic.beta + t / cubic.srtt * cubic.SMSS

        print(f"{t:<10.1f} {W_cubic:<15.1f} {W_tcp:<15.1f} {W_reno:<15.1f}")

    # 4. 统计
    print("\n4. Final Statistics:")
    print("-" * 40)
    print(f"  Algorithm: CUBIC")
    print(f"  C: {cubic.C}")
    print(f"  β: {cubic.beta}")
    print(f"  RTT: {cubic.srtt}s")
    print(f"  Loss events: {cubic.loss_events}")
```

---

## 8. 现代应用

### 8.1 CUBIC部署

#### 8.1.1 操作系统支持

- **Linux**: 默认拥塞控制算法（2.6.19+）
- **Windows**: 可选算法
- **macOS**: 支持

#### 8.1.2 网络场景

- 数据中心间传输
- 高带宽卫星链路
- 跨洋传输
- 5G网络

### 8.2 CUBIC演进

#### 8.2.1 CUBIC变体

| 变体 | 特点 |
|------|------|
| CUBIC-Hystart | 混合启动，更快退出慢启动 |
| CUBIC+ECN | 结合显式拥塞通知 |
| QUIC CUBIC | RFC 9002定义 |

#### 8.2.2 对比现代算法

```
算法对比 (10Gbps, 100ms RTT):

算法      吞吐量     公平性     稳定性
-----     -------    ------    ----
Reno      15%        好        差
CUBIC     85%        好        好
BBR       95%        中        好
DCTCP     98%        好        好

CUBIC优势：
- 向后兼容
- 稳定成熟
- 广泛部署
```

### 8.3 与相关RFC的关系

| RFC | 主题 | 与RFC 8312关系 |
|-----|------|---------------|
| RFC 5681 | TCP拥塞控制 | 基础规范 |
| RFC 3390 | 初始窗口 | 慢启动配合 |
| RFC 9002 | QUIC CUBIC | QUIC适配 |

### 8.4 教学与研究价值

1. **数学建模**: 三次方函数在协议中的应用
2. **性能优化**: BDP网络优化策略
3. **公平性**: 多流公平性保证机制
4. **工程实践**: 从研究到部署的转化

---

## 参考文献

1. Ha, S., Rhee, I., and L. Xu. "CUBIC for Fast Long-Distance Networks." RFC 8312, February 2018.
2. Ha, S., Rhee, I., and L. Xu. "CUBIC: A New TCP-Friendly High-Speed TCP Variant." ACM SIGOPS Operating Systems Review, 2008.
3. Cardwell, N., et al. "BBR: Congestion-Based Congestion Control." ACM Queue, 2016.
4. Iyengar, J. and I. Swett. "QUIC Loss Detection and Congestion Control." RFC 9002, May 2021.

---

_文档版本: 1.0_
_最后更新: 2026年_
_状态: 核心RFC映射完成_
