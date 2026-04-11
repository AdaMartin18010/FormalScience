"""
生产者-消费者模型示例

演示经典的并发编程问题：
- 生产者生成数据放入缓冲区
- 消费者从缓冲区取出数据
- 缓冲区有容量限制
"""

import sys
sys.path.append('..')

from petri_net import PetriNet
from visualizer import TextVisualizer, AnimationSimulator


def create_producer_consumer_net(buffer_size: int = 3, num_items: int = 10) -> PetriNet:
    """
    创建生产者-消费者 Petri 网
    
    Args:
        buffer_size: 缓冲区大小
        num_items: 要生产的物品数量
        
    Returns:
        PetriNet 实例
    """
    net = PetriNet(f"ProducerConsumer_Buffer{buffer_size}")
    
    # === 生产者部分 ===
    net.add_place("producer_idle", tokens=1)  # 生产者空闲
    net.add_place("producer_busy", tokens=0)  # 生产者工作中
    net.add_place("items_to_produce", tokens=num_items)  # 待生产物品数
    
    net.add_transition("start_produce")
    net.add_transition("finish_produce")
    
    # 开始生产
    net.add_arc("producer_idle", "start_produce")
    net.add_arc("items_to_produce", "start_produce", weight=0)  # 只读检查
    net.add_arc("start_produce", "producer_busy")
    
    # 完成生产
    net.add_arc("producer_busy", "finish_produce")
    net.add_arc("finish_produce", "producer_idle")
    
    # === 缓冲区部分 ===
    net.add_place("buffer", tokens=0, capacity=buffer_size)  # 缓冲区
    net.add_place("buffer_slots", tokens=buffer_size)  # 可用槽位
    
    # 将物品放入缓冲区
    net.add_arc("finish_produce", "buffer")
    net.add_arc("buffer_slots", "finish_produce")
    
    # === 消费者部分 ===
    net.add_place("consumer_idle", tokens=1)  # 消费者空闲
    net.add_place("consumer_busy", tokens=0)  # 消费者工作中
    net.add_place("items_consumed", tokens=0)  # 已消费物品数
    
    net.add_transition("start_consume")
    net.add_transition("finish_consume")
    
    # 开始消费（需要缓冲区有物品）
    net.add_arc("consumer_idle", "start_consume")
    net.add_arc("buffer", "start_consume")
    net.add_arc("start_consume", "consumer_busy")
    
    # 完成消费
    net.add_arc("consumer_busy", "finish_consume")
    net.add_arc("finish_consume", "consumer_idle")
    net.add_arc("finish_consume", "buffer_slots")  # 释放槽位
    net.add_arc("finish_consume", "items_consumed")
    
    return net


def demo_basic():
    """基础演示"""
    print("=" * 70)
    print("生产者-消费者模型 - 基础演示")
    print("=" * 70)
    
    net = create_producer_consumer_net(buffer_size=3, num_items=8)
    viz = TextVisualizer(net)
    
    print("\n网络说明:")
    print("  - 生产者: 可以生产 8 个物品")
    print("  - 缓冲区: 容量为 3")
    print("  - 消费者: 消费缓冲区中的物品")
    
    print("\n初始状态:")
    viz.print()
    
    print("\n模拟执行 (自动):")
    step = 0
    while True:
        enabled = net.get_enabled_transitions()
        if not enabled:
            print(f"\n步 {step}: 无可用变迁（模拟结束）")
            break
        
        # 优先选择生产相关或消费相关
        produce_trans = [t for t in enabled if "produce" in t]
        consume_trans = [t for t in enabled if "consume" in t]
        
        if produce_trans and step % 3 != 2:  # 2/3 概率生产
            fired = sorted(produce_trans)[0]
        elif consume_trans:
            fired = sorted(consume_trans)[0]
        else:
            fired = sorted(enabled)[0]
        
        net.fire(fired)
        step += 1
        
        buffer_level = net.places["buffer"].tokens
        remaining = net.places["items_to_produce"].tokens
        consumed = net.places["items_consumed"].tokens
        
        print(f"步 {step:2d}: {fired:15} | 缓冲区: {buffer_level}/3 | "
              f"待生产: {remaining} | 已消费: {consumed}")
        
        if step >= 30:  # 限制步数
            print("\n(达到最大步数限制)")
            break
    
    print("\n最终状态:")
    viz.print()
    
    total_produced = net.places["buffer"].tokens + net.places["items_consumed"].tokens
    print(f"\n统计:")
    print(f"  - 总生产: {total_produced} 个")
    print(f"  - 缓冲区中: {net.places['buffer'].tokens} 个")
    print(f"  - 已消费: {net.places['items_consumed'].tokens} 个")


def demo_comparison():
    """比较不同缓冲区大小"""
    print("\n" + "=" * 70)
    print("不同缓冲区大小的比较")
    print("=" * 70)
    
    buffer_sizes = [1, 2, 3, 5, 10]
    num_items = 20
    
    print(f"\n测试场景: 生产 {num_items} 个物品，不同缓冲区大小")
    print(f"\n{'缓冲区大小':<12} {'总步数':<10} {'效率':<10}")
    print("-" * 35)
    
    for size in buffer_sizes:
        net = create_producer_consumer_net(buffer_size=size, num_items=num_items)
        
        steps = 0
        max_steps = 100
        
        while steps < max_steps:
            enabled = net.get_enabled_transitions()
            if not enabled:
                break
            net.fire_any()
            steps += 1
        
        consumed = net.places["items_consumed"].tokens
        efficiency = consumed / num_items * 100
        
        print(f"{size:<12} {steps:<10} {efficiency:>6.1f}%")
    
    print("\n💡 结论: 缓冲区越大，生产者和消费者越能并行工作")


def demo_deadlock():
    """演示死锁场景"""
    print("\n" + "=" * 70)
    print("死锁场景演示")
    print("=" * 70)
    
    print("\n场景: 缓冲区已满且消费者故障")
    
    net = PetriNet("DeadlockScenario")
    
    # 缓冲区已满
    net.add_place("buffer", tokens=3, capacity=3)
    
    # 生产者想继续生产
    net.add_place("producer", tokens=1)
    net.add_transition("produce")
    net.add_arc("producer", "produce")
    # 没有可用的缓冲区槽位！
    
    # 消费者故障（不能消费）
    net.add_place("consumer_broken", tokens=1)
    net.add_place("items_consumed", tokens=0)
    # 没有消费变迁！
    
    viz = TextVisualizer(net)
    print("\n初始状态:")
    viz.print()
    
    print("\n分析:")
    print("  - 缓冲区已满 (3/3)")
    print("  - 生产者无法生产（没有空闲槽位）")
    print("  - 消费者故障（无法消费）")
    print("  - 结果: 死锁！")
    
    if net.is_deadlocked():
        print("\n✓ 已检测到死锁")
    
    print("\n解决方案:")
    print("  1. 修复消费者，使其能正常消费")
    print("  2. 使用阻塞机制等待缓冲区可用")
    print("  3. 丢弃超额生产（有损处理）")


def demo_interactive():
    """交互式演示"""
    print("\n" + "=" * 70)
    print("交互式演示")
    print("=" * 70)
    
    net = create_producer_consumer_net(buffer_size=2, num_items=5)
    simulator = AnimationSimulator(net)
    
    print("\n提示:")
    print("  - 输入变迁名称触发")
    print("  - 'auto' 自动运行")
    print("  - 'quit' 退出")
    
    try:
        simulator.run_interactive()
    except KeyboardInterrupt:
        print("\n已取消")


def main():
    """主函数"""
    print("\n" + "=" * 70)
    print("生产者-消费者模型示例")
    print("=" * 70)
    
    import sys
    
    if len(sys.argv) > 1:
        if sys.argv[1] == "basic":
            demo_basic()
        elif sys.argv[1] == "compare":
            demo_comparison()
        elif sys.argv[1] == "deadlock":
            demo_deadlock()
        elif sys.argv[1] == "interactive":
            demo_interactive()
        else:
            print(f"未知命令: {sys.argv[1]}")
            print("可用命令: basic, compare, deadlock, interactive")
    else:
        # 运行所有演示
        demo_basic()
        demo_comparison()
        demo_deadlock()
        
        print("\n" + "=" * 70)
        print("所有演示完成！")
        print("=" * 70)
        print("\n运行 'python producer_consumer.py interactive' 进行交互式演示")


if __name__ == "__main__":
    main()
