"""
哲学家就餐问题示例

经典的死锁示例：
- 5位哲学家围坐在圆桌旁
- 每位哲学家需要左右两只叉子才能就餐
- 如果不加控制，可能发生死锁（所有哲学家都拿起左边的叉子，等待右边的叉子）
"""

import sys
sys.path.append('..')

from petri_net import PetriNet
from visualizer import TextVisualizer, AnimationSimulator


def create_naive_solution(n: int = 5) -> PetriNet:
    """
    创建朴素的哲学家就餐 Petri 网（可能死锁）
    
    每位哲学家：
    1. 拿起左叉子
    2. 拿起右叉子
    3. 就餐
    4. 放下叉子
    
    这种策略可能导致死锁
    """
    net = PetriNet(f"DiningPhilosophers_Naive_{n}")
    
    # 创建哲学家和叉子
    for i in range(n):
        # 哲学家状态
        net.add_place(f"think_{i}", tokens=1)  # 思考中
        net.add_place(f"has_left_{i}", tokens=0)  # 持有左叉子
        net.add_place(f"eat_{i}", tokens=0)  # 就餐中
        
        # 叉子
        net.add_place(f"fork_{i}", tokens=1)  # 叉子在桌上
    
    # 创建变迁
    for i in range(n):
        left_fork = f"fork_{i}"
        right_fork = f"fork_{(i+1) % n}"
        
        # 拿起左叉子
        net.add_transition(f"take_left_{i}")
        net.add_arc(f"think_{i}", f"take_left_{i}")
        net.add_arc(left_fork, f"take_left_{i}")
        net.add_arc(f"take_left_{i}", f"has_left_{i}")
        
        # 拿起右叉子（需要已经拿着左叉子）
        net.add_transition(f"take_right_{i}")
        net.add_arc(f"has_left_{i}", f"take_right_{i}")
        net.add_arc(right_fork, f"take_right_{i}")
        net.add_arc(f"take_right_{i}", f"eat_{i}")
        
        # 放下叉子并回到思考
        net.add_transition(f"release_{i}")
        net.add_arc(f"eat_{i}", f"release_{i}")
        net.add_arc(f"release_{i}", left_fork)
        net.add_arc(f"release_{i}", right_fork)
        net.add_arc(f"release_{i}", f"think_{i}")
    
    return net


def create_arbitrator_solution(n: int = 5) -> PetriNet:
    """
    使用仲裁者（服务员）的解决方案
    
    引入一个全局令牌（服务员），同一时间只允许一位哲学家尝试拿叉子
    """
    net = PetriNet(f"DiningPhilosophers_Arbitrator_{n}")
    
    # 服务员令牌（互斥）
    net.add_place("waiter", tokens=1)
    
    # 创建哲学家和叉子
    for i in range(n):
        net.add_place(f"think_{i}", tokens=1)
        net.add_place(f"eat_{i}", tokens=0)
        net.add_place(f"fork_{i}", tokens=1)
    
    # 创建变迁
    for i in range(n):
        left_fork = f"fork_{i}"
        right_fork = f"fork_{(i+1) % n}"
        
        # 请求就餐（获取服务员许可）
        net.add_transition(f"request_{i}")
        net.add_arc(f"think_{i}", f"request_{i}")
        net.add_arc("waiter", f"request_{i}")
        net.add_arc(left_fork, f"request_{i}")
        net.add_arc(right_fork, f"request_{i}")
        net.add_arc(f"request_{i}", f"eat_{i}")
        
        # 释放（归还服务员许可）
        net.add_transition(f"release_{i}")
        net.add_arc(f"eat_{i}", f"release_{i}")
        net.add_arc(f"release_{i}", left_fork)
        net.add_arc(f"release_{i}", right_fork)
        net.add_arc(f"release_{i}", "waiter")
        net.add_arc(f"release_{i}", f"think_{i}")
    
    return net


def create_hierarchy_solution(n: int = 5) -> PetriNet:
    """
    使用资源分级（Resource Hierarchy）的解决方案
    
    为叉子编号，哲学家总是先拿编号小的叉子
    """
    net = PetriNet(f"DiningPhilosophers_Hierarchy_{n}")
    
    for i in range(n):
        net.add_place(f"think_{i}", tokens=1)
        net.add_place(f"eat_{i}", tokens=0)
        net.add_place(f"fork_{i}", tokens=1)
    
    for i in range(n):
        left_fork = f"fork_{i}"
        right_fork = f"fork_{(i+1) % n}"
        
        # 确定先拿哪只叉子（编号小的）
        if i < (i+1) % n:
            first, second = left_fork, right_fork
            first_trans, second_trans = f"take_first_{i}", f"take_second_{i}"
        else:
            first, second = right_fork, left_fork
            first_trans, second_trans = f"take_first_{i}", f"take_second_{i}"
        
        # 拿第一只叉子
        net.add_transition(first_trans)
        net.add_arc(f"think_{i}", first_trans)
        net.add_arc(first, first_trans)
        net.add_arc(first_trans, f"has_first_{i}")
        net.add_place(f"has_first_{i}", tokens=0)
        
        # 拿第二只叉子
        net.add_transition(second_trans)
        net.add_arc(f"has_first_{i}", second_trans)
        net.add_arc(second, second_trans)
        net.add_arc(second_trans, f"eat_{i}")
        
        # 放下叉子
        net.add_transition(f"release_{i}")
        net.add_arc(f"eat_{i}", f"release_{i}")
        net.add_arc(f"release_{i}", left_fork)
        net.add_arc(f"release_{i}", right_fork)
        net.add_arc(f"release_{i}", f"think_{i}")
    
    return net


def demo_naive():
    """演示朴素方案（可能死锁）"""
    print("=" * 70)
    print("哲学家就餐问题 - 朴素方案（可能死锁）")
    print("=" * 70)
    
    n = 3  # 使用3位哲学家，便于演示
    net = create_naive_solution(n)
    viz = TextVisualizer(net)
    
    print(f"\n{n} 位哲学家，每人需要 2 只叉子才能就餐")
    print("\n策略: 先拿左叉子，再拿右叉子")
    print("⚠️  这种策略可能导致死锁！")
    
    print("\n初始状态:")
    viz.print()
    
    print("\n模拟执行（尝试触发死锁）:")
    
    # 尝试让所有哲学家同时拿起左叉子
    for i in range(n):
        trans = f"take_left_{i}"
        if net.is_enabled(trans):
            net.fire(trans)
            print(f"  哲学家 {i} 拿起了左叉子")
    
    print("\n此时状态:")
    viz.print()
    
    print("\n结果分析:")
    enabled = net.get_enabled_transitions()
    
    # 检查是否有人能拿起右叉子
    can_take_right = [t for t in enabled if "take_right" in t]
    
    if can_take_right:
        print(f"  ✓ 还有 {len(can_take_right)} 位哲学家能拿起右叉子")
        print("  （这不是最坏情况）")
    else:
        print("  ⚠️  没有人能拿起右叉子！")
        print("  （如果所有人都拿着左叉子等待右叉子，就是死锁）")
    
    if net.is_deadlocked():
        print("\n  ❌ 检测到死锁！")
    
    # 继续运行看是否会死锁
    print("\n继续运行...")
    steps = net.run(max_steps=20)
    
    print(f"\n运行了 {steps} 步后:")
    viz.print()
    
    if net.is_deadlocked():
        print("\n❌ 死锁！系统无法继续")
        print("\n死锁原因:")
        for i in range(n):
            has_left = net.places.get(f"has_left_{i}", Place("", 0)).tokens > 0
            if has_left:
                print(f"  - 哲学家 {i}: 持有左叉子，等待右叉子")


def demo_solutions():
    """演示解决方案"""
    print("\n" + "=" * 70)
    print("死锁解决方案")
    print("=" * 70)
    
    solutions = [
        ("仲裁者 (Arbitrator)", create_arbitrator_solution(3)),
        ("资源分级 (Resource Hierarchy)", create_hierarchy_solution(3)),
    ]
    
    for name, net in solutions:
        print(f"\n{name}:")
        print("-" * 50)
        
        viz = TextVisualizer(net)
        
        # 运行模拟
        steps = 0
        max_steps = 30
        eat_count = [0] * 3
        
        while steps < max_steps:
            enabled = net.get_enabled_transitions()
            if not enabled:
                break
            
            fired = net.fire_any()
            steps += 1
            
            # 记录就餐次数
            for i in range(3):
                if f"eat_{i}" in fired or (f"request_{i}" in fired if "Arbitrator" in name else False):
                    eat_count[i] += 1
        
        print(f"  执行了 {steps} 步")
        print(f"  每位哲学家的就餐次数: {eat_count}")
        
        if net.is_deadlocked():
            print("  ⚠️  死锁！")
        else:
            print("  ✓ 无死锁")
        
        print(f"\n  最终状态: {viz.render_compact()}")


def demo_comparison():
    """比较不同方案"""
    print("\n" + "=" * 70)
    print("方案比较")
    print("=" * 70)
    
    n = 5
    scenarios = [
        ("朴素方案", create_naive_solution(n)),
        ("仲裁者", create_arbitrator_solution(n)),
        ("资源分级", create_hierarchy_solution(n)),
    ]
    
    print(f"\n{n} 位哲学家，运行 50 步:")
    print(f"\n{'方案':<15} {'步数':<10} {'死锁':<10} {'公平性'}")
    print("-" * 50)
    
    for name, net in scenarios:
        # 复制网络以避免状态污染
        net_copy = net.clone()
        
        steps = net_copy.run(max_steps=50)
        deadlocked = net_copy.is_deadlocked()
        
        # 计算公平性（就餐次数的标准差）
        eat_counts = []
        for i in range(n):
            count = net_copy.places.get(f"eat_{i}", Place("", 0)).tokens
            eat_counts.append(count)
        
        # 简单公平性：最大差值
        fairness = max(eat_counts) - min(eat_counts) if eat_counts else 0
        fairness_str = f"差值={fairness}"
        
        deadlock_str = "是" if deadlocked else "否"
        
        print(f"{name:<15} {steps:<10} {deadlock_str:<10} {fairness_str}")


def demo_interactive():
    """交互式演示"""
    print("\n" + "=" * 70)
    print("交互式演示")
    print("=" * 70)
    
    net = create_naive_solution(3)
    simulator = AnimationSimulator(net)
    
    print("\n提示:")
    print("  - 尝试让所有哲学家都拿起左叉子")
    print("  - 观察是否会发生死锁")
    print("  - 'auto' 自动运行")
    
    try:
        simulator.run_interactive()
    except KeyboardInterrupt:
        print("\n已取消")


def main():
    """主函数"""
    print("\n" + "=" * 70)
    print("哲学家就餐问题示例")
    print("Dining Philosophers Problem")
    print("=" * 70)
    
    import sys
    
    if len(sys.argv) > 1:
        cmd = sys.argv[1]
        if cmd == "naive":
            demo_naive()
        elif cmd == "solutions":
            demo_solutions()
        elif cmd == "compare":
            demo_comparison()
        elif cmd == "interactive":
            demo_interactive()
        else:
            print(f"未知命令: {cmd}")
            print("可用: naive, solutions, compare, interactive")
    else:
        demo_naive()
        demo_solutions()
        demo_comparison()
        
        print("\n" + "=" * 70)
        print("所有演示完成！")
        print("=" * 70)
        print("\n运行 'python dining_philosophers.py interactive' 进行交互式演示")


# 导入 Place 类
def Place(name: str, tokens: int):
    """辅助函数创建 Place"""
    from petri_net import Place as P
    return P(name, tokens)


if __name__ == "__main__":
    main()
