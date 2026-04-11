# Petri Net Simulator - Petri网模拟器

一个用 Python 实现的 Petri 网模拟器，支持基本 Petri 网的建模、仿真和可视化。

## 什么是 Petri 网？

Petri 网是一种数学建模语言，用于描述分布式系统。它由以下元素组成：

- **Place（库所）**: 用圆形表示，代表系统的状态或条件
- **Transition（变迁）**: 用矩形/条形表示，代表事件或动作
- **Arc（弧）**: 用箭头表示，连接库所和变迁
- **Token（令牌）**: 用黑点表示，位于库所中，代表状态的具体实例

## 项目结构

```
petri_net_simulator/
├── README.md
├── main.py              # 主程序入口
├── petri_net.py         # Petri 网核心实现
├── visualizer.py        # 可视化模块
└── examples/
    ├── simple.py        # 简单示例
    ├── producer_consumer.py  # 生产者-消费者模型
    └── dining_philosophers.py # 哲学家就餐问题
```

## 运行方式

```bash
# 运行主程序
python main.py

# 运行示例
python examples/simple.py
python examples/producer_consumer.py
python examples/dining_philosophers.py
```

## 示例模型

### 1. 简单模型

基本的令牌传递演示

### 2. 生产者-消费者模型

经典的多线程同步问题

### 3. 哲学家就餐问题

经典的死锁示例

## 核心功能

- ✅ 创建和编辑 Petri 网
- ✅ 模拟执行（手动/自动步进）
- ✅ 检测可触发变迁
- ✅ 检查死锁
- ✅ 可视化显示
- ✅ 状态历史记录

## 许可证

MIT License
