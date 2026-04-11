"""
Petri 网核心实现模块

提供 Petri 网的基本数据结构和模拟算法。
"""

from typing import Dict, List, Set, Tuple, Optional, Iterator
from dataclasses import dataclass, field
from collections import defaultdict
import copy


@dataclass
class Place:
    """
    库所（Place）类
    
    库所代表系统的状态或条件，可以包含一定数量的令牌（Token）。
    
    Attributes:
        name: 库所的唯一标识符
        tokens: 当前令牌数量（标记）
        capacity: 容量限制（None 表示无限制）
    """
    name: str
    tokens: int = 0
    capacity: Optional[int] = None
    
    def __post_init__(self):
        """初始化后验证令牌数量"""
        if self.tokens < 0:
            raise ValueError(f"初始令牌数量不能为负数: {self.tokens}")
        if self.capacity is not None and self.tokens > self.capacity:
            raise ValueError(f"初始令牌数量超过容量: {self.tokens} > {self.capacity}")
    
    def can_add(self, amount: int) -> bool:
        """检查是否可以添加指定数量的令牌"""
        if self.capacity is None:
            return True
        return self.tokens + amount <= self.capacity
    
    def add_tokens(self, amount: int) -> None:
        """添加令牌"""
        if amount < 0:
            raise ValueError(f"不能添加负数的令牌: {amount}")
        if not self.can_add(amount):
            raise ValueError(f"超出容量限制: {self.tokens} + {amount} > {self.capacity}")
        self.tokens += amount
    
    def remove_tokens(self, amount: int) -> None:
        """移除令牌"""
        if amount < 0:
            raise ValueError(f"不能移除负数的令牌: {amount}")
        if self.tokens < amount:
            raise ValueError(f"令牌不足: {self.tokens} < {amount}")
        self.tokens -= amount
    
    def has_tokens(self, amount: int = 1) -> bool:
        """检查是否有足够数量的令牌"""
        return self.tokens >= amount
    
    def __str__(self) -> str:
        cap_str = f"/{self.capacity}" if self.capacity else ""
        return f"Place({self.name}): {self.tokens}{cap_str} tokens"


@dataclass
class Transition:
    """
    变迁（Transition）类
    
    变迁代表系统的事件或动作，当输入库所有足够的令牌时，
    变迁可以被触发，从而消耗输入令牌并产生输出令牌。
    
    Attributes:
        name: 变迁的唯一标识符
    """
    name: str
    
    def __str__(self) -> str:
        return f"Transition({self.name})"


@dataclass
class Arc:
    """
    弧（Arc）类
    
    弧连接库所和变迁，表示令牌的流动方向。
    
    Attributes:
        source: 起点（库所或变迁的名称）
        target: 终点（变迁或库所的名称）
        weight: 弧的权重（默认1）
    """
    source: str
    target: str
    weight: int = 1
    
    def __post_init__(self):
        """验证权重"""
        if self.weight <= 0:
            raise ValueError(f"弧权重必须为正数: {self.weight}")
    
    def __str__(self) -> str:
        return f"Arc({self.source} -> {self.target}, weight={self.weight})"


@dataclass
class Marking:
    """
    标记（Marking）类
    
    表示 Petri 网在某个时刻的全局状态，
    即所有库所的令牌分布。
    """
    tokens: Dict[str, int] = field(default_factory=dict)
    
    def get(self, place_name: str) -> int:
        """获取指定库所的令牌数量"""
        return self.tokens.get(place_name, 0)
    
    def set(self, place_name: str, amount: int) -> None:
        """设置指定库所的令牌数量"""
        self.tokens[place_name] = amount
    
    def copy(self) -> 'Marking':
        """创建标记的副本"""
        return Marking(self.tokens.copy())
    
    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Marking):
            return False
        return self.tokens == other.tokens
    
    def __hash__(self) -> int:
        return hash(tuple(sorted(self.tokens.items())))
    
    def __str__(self) -> str:
        items = [f"{place}={tokens}" for place, tokens in sorted(self.tokens.items())]
        return f"Marking({', '.join(items)})"


class PetriNet:
    """
    Petri 网主类
    
    管理库所、变迁和弧，并提供模拟执行功能。
    
    Attributes:
        name: Petri 网名称
        places: 库所字典
        transitions: 变迁字典
        input_arcs: 输入弧（库所 -> 变迁）
        output_arcs: 输出弧（变迁 -> 库所）
        history: 状态历史记录
    """
    
    def __init__(self, name: str = "PetriNet"):
        """
        创建新的 Petri 网
        
        Args:
            name: Petri 网名称
        """
        self.name = name
        self.places: Dict[str, Place] = {}
        self.transitions: Dict[str, Transition] = {}
        self.input_arcs: Dict[str, List[Arc]] = defaultdict(list)  # place_name -> arcs
        self.output_arcs: Dict[str, List[Arc]] = defaultdict(list)  # transition_name -> arcs
        self.reverse_input: Dict[str, List[Arc]] = defaultdict(list)  # transition_name -> arcs
        self.reverse_output: Dict[str, List[Arc]] = defaultdict(list)  # place_name -> arcs
        self.history: List[Tuple[str, Marking]] = []  # (transition_name, marking)
        self.step_count: int = 0
    
    def add_place(self, name: str, tokens: int = 0, capacity: Optional[int] = None) -> Place:
        """
        添加库所
        
        Args:
            name: 库所名称
            tokens: 初始令牌数量
            capacity: 容量限制
            
        Returns:
            创建的库所对象
        """
        if name in self.places:
            raise ValueError(f"库所已存在: {name}")
        
        place = Place(name, tokens, capacity)
        self.places[name] = place
        return place
    
    def add_transition(self, name: str) -> Transition:
        """
        添加变迁
        
        Args:
            name: 变迁名称
            
        Returns:
            创建的变迁对象
        """
        if name in self.transitions:
            raise ValueError(f"变迁已存在: {name}")
        
        transition = Transition(name)
        self.transitions[name] = transition
        return transition
    
    def add_arc(self, source: str, target: str, weight: int = 1) -> Arc:
        """
        添加弧
        
        弧必须连接库所和变迁（不能库所到库所或变迁到变迁）
        
        Args:
            source: 起点名称
            target: 终点名称
            weight: 权重
            
        Returns:
            创建的弧对象
        """
        # 验证源和目标存在
        source_is_place = source in self.places
        source_is_transition = source in self.transitions
        target_is_place = target in self.places
        target_is_transition = target in self.transitions
        
        if not (source_is_place or source_is_transition):
            raise ValueError(f"源不存在: {source}")
        if not (target_is_place or target_is_transition):
            raise ValueError(f"目标不存在: {target}")
        
        # 验证连接类型（必须是 库所->变迁 或 变迁->库所）
        if source_is_place and target_is_place:
            raise ValueError("不能连接两个库所")
        if source_is_transition and target_is_transition:
            raise ValueError("不能连接两个变迁")
        
        arc = Arc(source, target, weight)
        
        if source_is_place:
            # 库所 -> 变迁（输入弧）
            self.input_arcs[source].append(arc)
            self.reverse_input[target].append(arc)
        else:
            # 变迁 -> 库所（输出弧）
            self.output_arcs[source].append(arc)
            self.reverse_output[target].append(arc)
        
        return arc
    
    def get_marking(self) -> Marking:
        """获取当前标记（状态）"""
        marking = Marking()
        for name, place in self.places.items():
            marking.set(name, place.tokens)
        return marking
    
    def set_marking(self, marking: Marking) -> None:
        """设置当前标记"""
        for place_name in self.places:
            self.places[place_name].tokens = marking.get(place_name)
    
    def is_enabled(self, transition_name: str) -> bool:
        """
        检查变迁是否可触发
        
        变迁可触发的条件：
        1. 所有输入库所都有足够的令牌
        2. 所有输出库所都有足够的容量接收新令牌
        
        Args:
            transition_name: 变迁名称
            
        Returns:
            是否可触发
        """
        if transition_name not in self.transitions:
            raise ValueError(f"变迁不存在: {transition_name}")
        
        # 检查输入库所
        for arc in self.reverse_input[transition_name]:
            place = self.places[arc.source]
            if not place.has_tokens(arc.weight):
                return False
        
        # 检查输出库所容量
        for arc in self.output_arcs[transition_name]:
            place = self.places[arc.target]
            if not place.can_add(arc.weight):
                return False
        
        return True
    
    def get_enabled_transitions(self) -> List[str]:
        """获取所有可触发的变迁名称"""
        return [name for name in self.transitions if self.is_enabled(name)]
    
    def fire(self, transition_name: str) -> bool:
        """
        触发变迁
        
        执行变迁：消耗输入令牌，产生输出令牌
        
        Args:
            transition_name: 要触发的变迁名称
            
        Returns:
            是否成功触发
        """
        if not self.is_enabled(transition_name):
            return False
        
        # 记录当前状态
        current_marking = self.get_marking()
        self.history.append((transition_name, current_marking))
        
        # 消耗输入令牌
        for arc in self.reverse_input[transition_name]:
            place = self.places[arc.source]
            place.remove_tokens(arc.weight)
        
        # 产生输出令牌
        for arc in self.output_arcs[transition_name]:
            place = self.places[arc.target]
            place.add_tokens(arc.weight)
        
        self.step_count += 1
        return True
    
    def fire_any(self) -> Optional[str]:
        """
        触发任意一个可触发的变迁
        
        Returns:
            触发的变迁名称，如果没有可触发的则返回 None
        """
        enabled = self.get_enabled_transitions()
        if enabled:
            # 按名称排序，保证确定性
            chosen = sorted(enabled)[0]
            self.fire(chosen)
            return chosen
        return None
    
    def run(self, max_steps: int = 100) -> int:
        """
        自动运行直到没有可触发的变迁或达到最大步数
        
        Args:
            max_steps: 最大执行步数
            
        Returns:
            实际执行的步数
        """
        steps = 0
        while steps < max_steps:
            if self.fire_any() is None:
                break
            steps += 1
        return steps
    
    def is_deadlocked(self) -> bool:
        """检查是否死锁（没有可触发的变迁）"""
        return len(self.get_enabled_transitions()) == 0
    
    def is_empty(self) -> bool:
        """检查所有库所是否都为空"""
        return all(place.tokens == 0 for place in self.places.values())
    
    def get_total_tokens(self) -> int:
        """获取网络中的总令牌数"""
        return sum(place.tokens for place in self.places.values())
    
    def reset(self) -> None:
        """重置网络到初始状态（清除历史和令牌）"""
        for place in self.places.values():
            place.tokens = 0
        self.history.clear()
        self.step_count = 0
    
    def clone(self) -> 'PetriNet':
        """创建网络的深拷贝"""
        new_net = PetriNet(f"{self.name}_copy")
        
        # 复制库所
        for name, place in self.places.items():
            new_net.add_place(name, place.tokens, place.capacity)
        
        # 复制变迁
        for name in self.transitions:
            new_net.add_transition(name)
        
        # 复制弧
        for arcs in self.input_arcs.values():
            for arc in arcs:
                new_net.add_arc(arc.source, arc.target, arc.weight)
        
        for arcs in self.output_arcs.values():
            for arc in arcs:
                # 避免重复添加（input_arcs 和 output_arcs 可能有重叠）
                pass
        
        return new_net
    
    def __str__(self) -> str:
        lines = [f"Petri Net: {self.name}", "=" * 40]
        
        lines.append("\nPlaces:")
        for name, place in sorted(self.places.items()):
            lines.append(f"  {place}")
        
        lines.append("\nTransitions:")
        for name in sorted(self.transitions.keys()):
            enabled = " [ENABLED]" if self.is_enabled(name) else ""
            lines.append(f"  {name}{enabled}")
        
        lines.append("\nArcs:")
        seen = set()
        for arcs in self.input_arcs.values():
            for arc in arcs:
                key = (arc.source, arc.target)
                if key not in seen:
                    lines.append(f"  {arc}")
                    seen.add(key)
        for arcs in self.output_arcs.values():
            for arc in arcs:
                key = (arc.source, arc.target)
                if key not in seen:
                    lines.append(f"  {arc}")
                    seen.add(key)
        
        lines.append(f"\nStep count: {self.step_count}")
        lines.append(f"Enabled transitions: {self.get_enabled_transitions()}")
        
        return "\n".join(lines)


class ReachabilityGraph:
    """
    可达性图
    
    分析 Petri 网的所有可达状态
    """
    
    def __init__(self, petri_net: PetriNet):
        """
        创建可达性图分析器
        
        Args:
            petri_net: 要分析的 Petri 网
        """
        self.petri_net = petri_net
        self.states: Set[Marking] = set()
        self.transitions: Dict[Tuple[Marking, Marking], str] = {}
    
    def build(self, max_depth: int = 100) -> None:
        """
        构建可达性图
        
        Args:
            max_depth: 最大搜索深度
        """
        initial = self.petri_net.get_marking()
        self._explore(initial, 0, max_depth)
    
    def _explore(self, marking: Marking, depth: int, max_depth: int) -> None:
        """递归探索状态空间"""
        if depth > max_depth or marking in self.states:
            return
        
        self.states.add(marking)
        
        # 尝试触发每个变迁
        for trans_name in self.petri_net.transitions:
            net_copy = self.petri_net.clone()
            net_copy.set_marking(marking.copy())
            
            if net_copy.fire(trans_name):
                new_marking = net_copy.get_marking()
                self.transitions[(marking, new_marking)] = trans_name
                self._explore(new_marking, depth + 1, max_depth)
    
    def get_reachable_states(self) -> Set[Marking]:
        """获取所有可达状态"""
        return self.states.copy()
    
    def is_reachable(self, target: Marking) -> bool:
        """检查目标状态是否可达"""
        return target in self.states


# 便捷函数
def create_simple_net() -> PetriNet:
    """
    创建一个简单的 Petri 网示例
    
    两个库所 p1, p2 和一个变迁 t1
    初始：p1 有 1 个令牌
    触发 t1：p1 失去 1 个令牌，p2 获得 1 个令牌
    """
    net = PetriNet("Simple")
    
    net.add_place("p1", tokens=1)
    net.add_place("p2", tokens=0)
    net.add_transition("t1")
    
    net.add_arc("p1", "t1")
    net.add_arc("t1", "p2")
    
    return net


def create_sequence_net(n: int = 3) -> PetriNet:
    """
    创建顺序执行的 Petri 网
    
    p1 -> t1 -> p2 -> t2 -> p3 -> ... -> tn -> pn+1
    
    Args:
        n: 变迁数量
    """
    net = PetriNet(f"Sequence_{n}")
    
    # 添加库所
    for i in range(n + 1):
        tokens = 1 if i == 0 else 0
        net.add_place(f"p{i}", tokens=tokens)
    
    # 添加变迁和弧
    for i in range(n):
        net.add_transition(f"t{i}")
        net.add_arc(f"p{i}", f"t{i}")
        net.add_arc(f"t{i}", f"p{i+1}")
    
    return net


def create_fork_join_net() -> PetriNet:
    """
    创建 Fork-Join 结构的 Petri 网
    
         --> t1 --> p2 --> t3 -->
       /                          \
    p1                              p5
       \\                          /
         --> t2 --> p3 --> t4 -->
    
    这是一个并行结构，令牌从 p1 分叉，经过并行路径后汇合到 p5
    """
    net = PetriNet("ForkJoin")
    
    # 添加库所
    net.add_place("p1", tokens=1)
    net.add_place("p2", tokens=0)
    net.add_place("p3", tokens=0)
    net.add_place("p4", tokens=0)
    net.add_place("p5", tokens=0)
    
    # 添加变迁
    net.add_transition("fork")
    net.add_transition("work1")
    net.add_transition("work2")
    net.add_transition("join")
    
    # 添加弧
    net.add_arc("p1", "fork", weight=2)  # 产生两个令牌
    net.add_arc("fork", "p2")
    net.add_arc("fork", "p3")
    net.add_arc("p2", "work1")
    net.add_arc("work1", "p4")
    net.add_arc("p3", "work2")
    net.add_arc("work2", "p4")
    net.add_arc("p4", "join", weight=2)  # 需要两个令牌
    net.add_arc("join", "p5")
    
    return net


# 测试
if __name__ == "__main__":
    print("测试 Petri 网模块\n")
    
    # 测试简单网络
    print("=" * 50)
    print("测试简单网络")
    print("=" * 50)
    
    net = create_simple_net()
    print(net)
    print()
    
    print("触发 t1...")
    net.fire("t1")
    print(net)
    print()
    
    # 测试顺序网络
    print("=" * 50)
    print("测试顺序网络")
    print("=" * 50)
    
    seq_net = create_sequence_net(3)
    print(seq_net)
    print()
    
    print("自动运行...")
    steps = seq_net.run()
    print(f"执行了 {steps} 步")
    print(seq_net)
    print()
    
    # 测试 Fork-Join 网络
    print("=" * 50)
    print("测试 Fork-Join 网络")
    print("=" * 50)
    
    fj_net = create_fork_join_net()
    print(fj_net)
    print()
    
    print("逐步执行:")
    while True:
        enabled = fj_net.get_enabled_transitions()
        if not enabled:
            break
        fired = fj_net.fire_any()
        print(f"  触发 {fired}: {fj_net.get_marking()}")
    
    print(f"\n最终状态: {fj_net.get_marking()}")
