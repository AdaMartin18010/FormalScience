"""
简单 Petri 网示例

演示最基本的 Petri 网概念：
- 库所（Places）
- 变迁（Transitions）
- 弧（Arcs）
- 令牌（Tokens）
"""

import sys
sys.path.append('..')

from petri_net import PetriNet, create_simple_net, create_sequence_net
from visualizer import TextVisualizer, AnimationSimulator


def example_1_basic():
    """示例 1: 最基本的令牌传递"""
    print("=" * 60)
    print("示例 1: 基本令牌传递 (Basic Token Passing)")
    print("=" * 60)
    
    net = PetriNet("BasicPassing")
    
    # 创建两个库所
    net.add_place("p1", tokens=3)
    net.add_place("p2", tokens=0)
    
    # 创建一个变迁
    net.add_transition("t1")
    
    # 创建弧：p1 -> t1 -> p2
    net.add_arc("p1", "t1")
    net.add_arc("t1", "p2")
    
    # 可视化
    viz = TextVisualizer(net)
    print("\n初始状态:")
    viz.print()
    
    print("\n执行过程:")
    while net.places["p1"].tokens > 0:
        net.fire("t1")
        print(f"  触发 t1 -> {viz.render_compact()}")
    
    print("\n最终状态:")
    viz.print()
    
    print(f"\n✓ 所有令牌已从 p1 转移到 p2")


def example_2_sequence():
    """示例 2: 顺序执行网络"""
    print("\n" + "=" * 60)
    print("示例 2: 顺序执行 (Sequential Execution)")
    print("=" * 60)
    
    net = create_sequence_net(4)
    viz = TextVisualizer(net)
    
    print("\n网络结构: p0 -> t0 -> p1 -> t1 -> p2 -> t2 -> p3")
    print("\n初始状态:")
    viz.print()
    
    print("\n自动执行:")
    steps = net.run()
    print(f"执行了 {steps} 步")
    
    print("\n最终状态:")
    viz.print()
    
    print("\n执行历史:")
    viz.print_history()


def example_3_choice():
    """示例 3: 选择结构"""
    print("\n" + "=" * 60)
    print("示例 3: 选择结构 (Choice/Conflict)")
    print("=" * 60)
    
    net = PetriNet("Choice")
    
    # 起始库所有一个令牌
    net.add_place("start", tokens=1)
    
    # 两个输出库所
    net.add_place("choice_a", tokens=0)
    net.add_place("choice_b", tokens=0)
    
    # 两个变迁（竞争同一个令牌）
    net.add_transition("select_a")
    net.add_transition("select_b")
    
    # 弧
    net.add_arc("start", "select_a")
    net.add_arc("start", "select_b")
    net.add_arc("select_a", "choice_a")
    net.add_arc("select_b", "choice_b")
    
    viz = TextVisualizer(net)
    print("\n网络结构:")
    print("         -> select_a -> choice_a")
    print("       /")
    print("  start")
    print("       \\")
    print("         -> select_b -> choice_b")
    print("\n这是一个冲突（conflict）结构")
    
    print("\n初始状态:")
    viz.print()
    
    print("\n注意：只有一个变迁可以触发（只有一个令牌）")
    
    # 尝试触发第一个可触发的变迁
    enabled = net.get_enabled_transitions()
    print(f"\n可触发的变迁: {enabled}")
    
    if enabled:
        chosen = enabled[0]
        net.fire(chosen)
        print(f"触发了: {chosen}")
        
        print("\n触发后的状态:")
        viz.print()
        
        print(f"\n观察: 选择 {chosen} 后，另一个变迁再也不能触发")


def example_4_weighted_arcs():
    """示例 4: 带权重的弧"""
    print("\n" + "=" * 60)
    print("示例 4: 带权重的弧 (Weighted Arcs)")
    print("=" * 60)
    
    net = PetriNet("WeightedArcs")
    
    # 源库所有很多令牌
    net.add_place("source", tokens=10)
    net.add_place("sink", tokens=0)
    
    # 变迁每次消耗/产生多个令牌
    net.add_transition("batch_process")
    
    # 权重为 3 的弧
    net.add_arc("source", "batch_process", weight=3)
    net.add_arc("batch_process", "sink", weight=3)
    
    viz = TextVisualizer(net)
    print("\n网络结构:")
    print("  source -(3)-> batch_process -(3)-> sink")
    print("\n每次触发消耗 3 个令牌，产生 3 个令牌")
    
    print("\n初始状态:")
    viz.print()
    
    print("\n执行过程:")
    while net.is_enabled("batch_process"):
        net.fire("batch_process")
        print(f"  触发 batch_process -> {viz.render_compact()}")
    
    print("\n无法再触发（剩余令牌少于 3 个）")
    print(f"\n最终状态:")
    viz.print()


def example_5_capacity():
    """示例 5: 容量限制"""
    print("\n" + "=" * 60)
    print("示例 5: 容量限制 (Capacity Constraints)")
    print("=" * 60)
    
    net = PetriNet("CapacityLimited")
    
    # 源
    net.add_place("source", tokens=10)
    
    # 目标有容量限制
    net.add_place("limited_buffer", tokens=0, capacity=5)
    
    net.add_transition("move")
    
    net.add_arc("source", "move")
    net.add_arc("move", "limited_buffer")
    
    viz = TextVisualizer(net)
    print("\n网络结构:")
    print("  source -(1)-> move -(1)-> limited_buffer (capacity=5)")
    
    print("\n初始状态:")
    viz.print()
    
    print("\n执行过程:")
    while net.is_enabled("move"):
        net.fire("move")
        buffer_tokens = net.places["limited_buffer"].tokens
        print(f"  触发 move -> buffer: {buffer_tokens}/5")
    
    print("\n无法继续（容量已满）")
    print(f"\n最终状态:")
    viz.print()
    print("\n💡 这种结构常用于建模有限缓冲区")


def main():
    """运行所有示例"""
    print("\n" + "=" * 60)
    print("Petri Net Simulator - 简单示例")
    print("=" * 60)
    
    example_1_basic()
    example_2_sequence()
    example_3_choice()
    example_4_weighted_arcs()
    example_5_capacity()
    
    print("\n" + "=" * 60)
    print("所有示例完成！")
    print("=" * 60)


if __name__ == "__main__":
    main()
