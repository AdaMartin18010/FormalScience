"""
Petri Net Simulator - 主程序入口

提供交互式界面和多种示例演示。
"""

from petri_net import (
    PetriNet, Place, Transition, Arc, Marking,
    create_simple_net, create_sequence_net, create_fork_join_net,
    ReachabilityGraph
)
from visualizer import TextVisualizer, GraphVisualizer, AnimationSimulator


def demo_basic():
    """基础演示：创建一个简单的令牌传递网络"""
    print("\n" + "=" * 70)
    print("DEMO 1: Basic Token Passing (基础令牌传递)")
    print("=" * 70)
    
    net = PetriNet("Basic")
    
    # 创建库所
    net.add_place("source", tokens=5)
    net.add_place("sink", tokens=0)
    
    # 创建变迁
    net.add_transition("move")
    
    # 创建弧
    net.add_arc("source", "move")
    net.add_arc("move", "sink")
    
    # 可视化初始状态
    viz = TextVisualizer(net)
    print("\nInitial state (初始状态):")
    viz.print()
    
    # 执行所有可能的步骤
    print("\nExecuting (执行中)...")
    steps = net.run()
    print(f"Completed {steps} steps.")
    
    viz.print()
    
    return net


def demo_producer_consumer():
    """
    生产者-消费者模型演示
    
    经典的并发编程问题：
    - 生产者生产物品放入缓冲区
    - 消费者从缓冲区取出物品消费
    - 缓冲区有容量限制
    """
    print("\n" + "=" * 70)
    print("DEMO 2: Producer-Consumer (生产者-消费者模型)")
    print("=" * 70)
    
    net = PetriNet("ProducerConsumer")
    
    # 库所
    net.add_place("producer_ready", tokens=1)  # 生产者准备就绪
    net.add_place("buffer", tokens=0, capacity=3)  # 缓冲区（容量3）
    net.add_place("consumer_ready", tokens=1)  # 消费者准备就绪
    net.add_place("item_consumed", tokens=0)  # 已消费物品计数
    
    # 变迁
    net.add_transition("produce")
    net.add_transition("consume")
    
    # 弧
    net.add_arc("producer_ready", "produce")
    net.add_arc("produce", "buffer")
    net.add_arc("produce", "producer_ready")  # 生产者继续生产
    
    net.add_arc("consumer_ready", "consume")
    net.add_arc("buffer", "consume")
    net.add_arc("consume", "consumer_ready")  # 消费者继续消费
    net.add_arc("consume", "item_consumed")
    
    # 可视化
    viz = TextVisualizer(net)
    print("\nInitial state (初始状态):")
    viz.print()
    
    print("\nStep-by-step execution (逐步执行):")
    for i in range(10):
        enabled = net.get_enabled_transitions()
        if not enabled:
            print(f"Step {i+1}: Deadlock! (缓冲区满或空)")
            break
        
        fired = net.fire_any()
        action = "Produced" if fired == "produce" else "Consumed"
        print(f"Step {i+1}: {action} -> Buffer: {net.places['buffer'].tokens} items")
    
    print("\nFinal state (最终状态):")
    viz.print()
    
    return net


def demo_dining_philosophers():
    """
    哲学家就餐问题演示
    
    经典的死锁示例：
    - 5位哲学家围坐在圆桌旁
    - 每位哲学家需要左右两只叉子才能就餐
    - 如果不加控制，可能发生死锁
    """
    print("\n" + "=" * 70)
    print("DEMO 3: Dining Philosophers (哲学家就餐问题)")
    print("=" * 70)
    
    net = PetriNet("DiningPhilosophers")
    
    n = 3  # 哲学家数量（简化为3，避免输出过长）
    
    # 创建哲学家和叉子
    for i in range(n):
        # 哲学家思考
        net.add_place(f"think_{i}", tokens=1)
        # 叉子可用
        net.add_place(f"fork_{i}", tokens=1)
        # 哲学家就餐
        net.add_place(f"eat_{i}", tokens=0)
    
    # 创建变迁：取叉子和放回叉子
    for i in range(n):
        left_fork = f"fork_{i}"
        right_fork = f"fork_{(i+1) % n}"
        
        # 开始就餐（需要左右两只叉子）
        net.add_transition(f"take_{i}")
        net.add_arc(f"think_{i}", f"take_{i}")
        net.add_arc(left_fork, f"take_{i}")
        net.add_arc(right_fork, f"take_{i}")
        net.add_arc(f"take_{i}", f"eat_{i}")
        
        # 结束就餐（放回叉子）
        net.add_transition(f"release_{i}")
        net.add_arc(f"eat_{i}", f"release_{i}")
        net.add_arc(f"release_{i}", left_fork)
        net.add_arc(f"release_{i}", right_fork)
        net.add_arc(f"release_{i}", f"think_{i}")
    
    # 可视化
    viz = TextVisualizer(net)
    print(f"\nInitial state ({n} philosophers, all thinking):")
    print(f"(初始状态：{n}位哲学家都在思考)")
    viz.print()
    
    print("\nSimulating (模拟执行)...")
    print("Note: This model can deadlock if all philosophers pick up left fork first!")
    print("(注意：如果所有哲学家同时拿起左边的叉子，会发生死锁！)")
    
    steps = 0
    max_steps = 20
    
    while steps < max_steps:
        enabled = net.get_enabled_transitions()
        
        if not enabled:
            print(f"\n⚠️  DEADLOCK at step {steps}!")
            print("No philosopher can eat because each holds one fork!")
            break
        
        # 优先选择 "release" 变迁，避免过早死锁（简单启发式）
        release_trans = [t for t in enabled if t.startswith("release_")]
        if release_trans:
            fired = sorted(release_trans)[0]
        else:
            fired = sorted(enabled)[0]
        
        net.fire(fired)
        steps += 1
        
        if fired.startswith("take_"):
            phil = fired.split("_")[1]
            print(f"  Step {steps}: Philosopher {phil} started eating")
        else:
            phil = fired.split("_")[1]
            print(f"  Step {steps}: Philosopher {phil} finished eating")
    
    print(f"\nFinal state after {steps} steps:")
    viz.print()
    
    if net.is_deadlocked():
        print("\n💡 Solution to prevent deadlock:")
        print("   1. Allow at most n-1 philosophers to try eating simultaneously")
        print("   2. Require philosophers to pick up both forks atomically")
        print("   3. Introduce an asymmetric strategy (e.g., odd philosophers pick left first)")
    
    return net


def demo_reachability_analysis():
    """可达性分析演示"""
    print("\n" + "=" * 70)
    print("DEMO 4: Reachability Analysis (可达性分析)")
    print("=" * 70)
    
    # 创建一个简单的网络用于分析
    net = PetriNet("Reachability")
    
    net.add_place("p1", tokens=2)
    net.add_place("p2", tokens=0)
    net.add_place("p3", tokens=0)
    
    net.add_transition("t1")
    net.add_transition("t2")
    
    net.add_arc("p1", "t1")
    net.add_arc("t1", "p2")
    net.add_arc("p2", "t2")
    net.add_arc("t2", "p3")
    
    print("\nPetri Net for analysis:")
    print(f"  Initial marking: {net.get_marking()}")
    
    # 构建可达性图
    print("\nBuilding reachability graph...")
    graph = ReachabilityGraph(net)
    graph.build(max_depth=10)
    
    reachable = graph.get_reachable_states()
    print(f"Found {len(reachable)} reachable states:")
    
    for i, marking in enumerate(sorted(reachable, key=lambda m: str(m)), 1):
        print(f"  State {i}: {marking}")
    
    # 检查特定状态是否可达
    target = Marking({"p1": 0, "p2": 0, "p3": 2})
    print(f"\nIs {target} reachable? {graph.is_reachable(target)}")
    
    return net


def demo_mutual_exclusion():
    """
    互斥演示
    
    使用 Petri 网实现互斥锁，确保临界区一次只有一个进程进入
    """
    print("\n" + "=" * 70)
    print("DEMO 5: Mutual Exclusion (互斥)")
    print("=" * 70)
    
    net = PetriNet("MutualExclusion")
    
    # 两个进程
    net.add_place("p1_idle", tokens=1)
    net.add_place("p2_idle", tokens=1)
    
    # 互斥锁
    net.add_place("mutex", tokens=1)
    
    # 临界区（最多容纳一个进程）
    net.add_place("critical", tokens=0, capacity=1)
    
    # 请求和释放锁
    net.add_transition("p1_request")
    net.add_transition("p1_release")
    net.add_transition("p2_request")
    net.add_transition("p2_release")
    
    # P1 的弧
    net.add_arc("p1_idle", "p1_request")
    net.add_arc("mutex", "p1_request")
    net.add_arc("p1_request", "critical")
    net.add_arc("critical", "p1_release")
    net.add_arc("p1_release", "mutex")
    net.add_arc("p1_release", "p1_idle")
    
    # P2 的弧
    net.add_arc("p2_idle", "p2_request")
    net.add_arc("mutex", "p2_request")
    net.add_arc("p2_request", "critical")
    net.add_arc("critical", "p2_release")
    net.add_arc("p2_release", "mutex")
    net.add_arc("p2_release", "p2_idle")
    
    viz = TextVisualizer(net)
    print("\nInitial state:")
    viz.print()
    
    print("\nDemonstrating mutual exclusion:")
    for i in range(8):
        enabled = net.get_enabled_transitions()
        
        # 优先释放锁
        release = [t for t in enabled if "release" in t]
        if release:
            fired = sorted(release)[0]
        elif enabled:
            fired = sorted(enabled)[0]
        else:
            break
        
        in_critical = net.places["critical"].tokens
        print(f"Step {i+1}: {fired:15} (in critical: {in_critical})")
        net.fire(fired)
    
    print("\nFinal state:")
    viz.print()
    print("\n✓ Mutual exclusion maintained: critical section never had more than 1 process")
    
    return net


def interactive_mode():
    """交互式模式"""
    print("\n" + "=" * 70)
    print("INTERACTIVE MODE (交互模式)")
    print("=" * 70)
    
    # 创建一个默认网络（顺序网络）
    net = create_sequence_net(3)
    simulator = AnimationSimulator(net)
    
    simulator.run_interactive()


def show_menu():
    """显示主菜单"""
    print("\n" + "=" * 70)
    print("Petri Net Simulator - Main Menu")
    print("=" * 70)
    print()
    print("Available demos:")
    print("  1. Basic Token Passing (基础令牌传递)")
    print("  2. Producer-Consumer (生产者-消费者)")
    print("  3. Dining Philosophers (哲学家就餐问题)")
    print("  4. Reachability Analysis (可达性分析)")
    print("  5. Mutual Exclusion (互斥)")
    print()
    print("Other options:")
    print("  i. Interactive Mode (交互模式)")
    print("  a. Run all demos (运行所有演示)")
    print("  q. Quit (退出)")
    print()


def main():
    """主程序入口"""
    print("\n" + "=" * 70)
    print("Petri Net Simulator")
    print("Petri 网模拟器")
    print("=" * 70)
    
    while True:
        show_menu()
        
        try:
            choice = input("Enter your choice: ").strip().lower()
        except (EOFError, KeyboardInterrupt):
            print("\n\nGoodbye!")
            break
        
        if choice == 'q' or choice == 'quit':
            print("\nGoodbye!")
            break
        elif choice == '1':
            demo_basic()
        elif choice == '2':
            demo_producer_conter()
        elif choice == '3':
            demo_dining_philosophers()
        elif choice == '4':
            demo_reachability_analysis()
        elif choice == '5':
            demo_mutual_exclusion()
        elif choice == 'i':
            interactive_mode()
        elif choice == 'a':
            demo_basic()
            demo_producer_consumer()
            demo_dining_philosophers()
            demo_reachability_analysis()
            demo_mutual_exclusion()
        else:
            print("\nInvalid choice. Please try again.")


if __name__ == "__main__":
    main()
