"""
Petri 网可视化模块

提供文本和图形化的 Petri 网显示功能。
"""

from typing import List, Optional, Tuple
from petri_net import PetriNet, Place, Transition, Marking
import os


class TextVisualizer:
    """文本可视化器 - 使用 ASCII 字符显示 Petri 网"""
    
    def __init__(self, petri_net: PetriNet):
        """
        创建文本可视化器
        
        Args:
            petri_net: 要可视化的 Petri 网
        """
        self.net = petri_net
    
    def render(self, show_enabled: bool = True) -> str:
        """
        渲染 Petri 网的文本表示
        
        Args:
            show_enabled: 是否标记可触发的变迁
            
        Returns:
            文本表示
        """
        lines = []
        lines.append(f"╔══════════════════════════════════════════════════════════════╗")
        lines.append(f"║  Petri Net: {self.net.name:49} ║")
        lines.append(f"╚══════════════════════════════════════════════════════════════╝")
        lines.append("")
        
        # 渲染库所
        lines.append("  Places (库所):")
        lines.append("  " + "─" * 60)
        
        for name in sorted(self.net.places.keys()):
            place = self.net.places[name]
            token_str = "●" * min(place.tokens, 10)
            if place.tokens > 10:
                token_str += f" (+{place.tokens - 10})"
            cap_str = f" [max: {place.capacity}]" if place.capacity else ""
            lines.append(f"    ○ {name:15} : {place.tokens:3d} tokens {token_str:20} {cap_str}")
        
        lines.append("")
        
        # 渲染变迁
        lines.append("  Transitions (变迁):")
        lines.append("  " + "─" * 60)
        
        for name in sorted(self.net.transitions.keys()):
            enabled = self.net.is_enabled(name)
            status = "▶ " if enabled and show_enabled else "  "
            enabled_str = " [可触发]" if enabled else ""
            lines.append(f"    {status}□ {name:15}{enabled_str}")
        
        lines.append("")
        
        # 渲染当前状态摘要
        lines.append("  Current State (当前状态):")
        lines.append("  " + "─" * 60)
        lines.append(f"    Total tokens: {self.net.get_total_tokens()}")
        lines.append(f"    Step count: {self.net.step_count}")
        lines.append(f"    Enabled transitions: {len(self.net.get_enabled_transitions())}")
        
        if self.net.is_deadlocked():
            lines.append("    ⚠️  DEADLOCKED (死锁)")
        
        lines.append("")
        
        return "\n".join(lines)
    
    def print(self, show_enabled: bool = True) -> None:
        """打印 Petri 网的文本表示"""
        print(self.render(show_enabled))
    
    def render_history(self, max_entries: int = 10) -> str:
        """
        渲染执行历史
        
        Args:
            max_entries: 最多显示的记录数
            
        Returns:
            历史记录的文本表示
        """
        lines = []
        lines.append("  Execution History (执行历史):")
        lines.append("  " + "─" * 60)
        
        if not self.net.history:
            lines.append("    (No steps executed yet)")
        else:
            start = max(0, len(self.net.history) - max_entries)
            for i, (trans, marking) in enumerate(self.net.history[start:], start=start):
                lines.append(f"    Step {i+1:3d}: {trans:15} -> {marking}")
            
            if len(self.net.history) > max_entries:
                lines.append(f"    ... ({len(self.net.history) - max_entries} earlier steps)")
        
        lines.append("")
        return "\n".join(lines)
    
    def print_history(self, max_entries: int = 10) -> None:
        """打印执行历史"""
        print(self.render_history(max_entries))
    
    def render_compact(self) -> str:
        """
        渲染紧凑状态表示
        
        Returns:
            紧凑的字符串表示
        """
        parts = []
        for name in sorted(self.net.places.keys()):
            place = self.net.places[name]
            parts.append(f"{name}:{place.tokens}")
        return "[" + ", ".join(parts) + "]"
    
    def print_step(self, transition_name: str) -> None:
        """
        打印单步执行的详细信息
        
        Args:
            transition_name: 触发的变迁名称
        """
        print(f"\n  Step {self.net.step_count}: Firing '{transition_name}'")
        print(f"  Before: {self.render_compact()}")
        
        success = self.net.fire(transition_name)
        
        if success:
            print(f"  After:  {self.render_compact()}")
        else:
            print(f"  Failed! Transition not enabled.")


class GraphVisualizer:
    """
    图形可视化器 - 生成 DOT 格式用于 Graphviz
    
    可以生成 .dot 文件，然后用 Graphviz 转换为图片
    """
    
    def __init__(self, petri_net: PetriNet):
        """
        创建图形可视化器
        
        Args:
            petri_net: 要可视化的 Petri 网
        """
        self.net = petri_net
    
    def to_dot(self, title: Optional[str] = None) -> str:
        """
        生成 DOT 格式字符串
        
        Args:
            title: 图表标题
            
        Returns:
            DOT 格式字符串
        """
        lines = []
        lines.append("digraph PetriNet {")
        lines.append(f'    label="{title or self.net.name}";')
        lines.append('    labelloc="t";')
        lines.append('    fontsize=20;')
        lines.append('    node [fontname="Arial"];')
        lines.append('    rankdir=LR;')  # 从左到右布局
        lines.append("")
        
        # 定义库所节点（圆形）
        lines.append("    // Places")
        for name, place in sorted(self.net.places.items()):
            # 根据令牌数量调整圆形大小
            size = max(0.3, min(1.0, 0.3 + place.tokens * 0.1))
            tokens_label = f"\\n({place.tokens})" if place.tokens > 0 else ""
            color = "lightblue" if place.tokens > 0 else "white"
            
            lines.append(
                f'    {name} [shape=circle, label="{name}{tokens_label}", '
                f'width={size}, height={size}, style=filled, fillcolor={color}];'
            )
        
        lines.append("")
        
        # 定义变迁节点（矩形）
        lines.append("    // Transitions")
        for name in sorted(self.net.transitions.keys()):
            enabled = self.net.is_enabled(name)
            color = "lightgreen" if enabled else "white"
            style = "filled,bold" if enabled else "filled"
            
            lines.append(
                f'    {name} [shape=box, label="{name}", '
                f'width=0.4, height=0.4, style="{style}", fillcolor={color}];'
            )
        
        lines.append("")
        
        # 添加弧
        lines.append("    // Arcs")
        seen = set()
        
        # 输入弧（库所 -> 变迁）
        for arcs in self.net.input_arcs.values():
            for arc in arcs:
                key = (arc.source, arc.target)
                if key not in seen:
                    weight_label = f" [label=\"{arc.weight}\"]" if arc.weight > 1 else ""
                    lines.append(f'    {arc.source} -> {arc.target}{weight_label};')
                    seen.add(key)
        
        # 输出弧（变迁 -> 库所）
        for arcs in self.net.output_arcs.values():
            for arc in arcs:
                key = (arc.source, arc.target)
                if key not in seen:
                    weight_label = f" [label=\"{arc.weight}\"]" if arc.weight > 1 else ""
                    lines.append(f'    {arc.source} -> {arc.target}{weight_label};')
                    seen.add(key)
        
        lines.append("}")
        
        return "\n".join(lines)
    
    def save_dot(self, filename: str, title: Optional[str] = None) -> None:
        """
        保存 DOT 文件
        
        Args:
            filename: 文件名
            title: 图表标题
        """
        dot_content = self.to_dot(title)
        with open(filename, 'w', encoding='utf-8') as f:
            f.write(dot_content)
        print(f"DOT file saved: {filename}")
    
    def render_image(self, output_file: str, format: str = "png") -> bool:
        """
        使用 Graphviz 渲染图片
        
        需要先安装 Graphviz：
        - Ubuntu/Debian: sudo apt-get install graphviz
        - macOS: brew install graphviz
        - Windows: choco install graphviz
        
        Args:
            output_file: 输出文件名
            format: 输出格式（png, svg, pdf 等）
            
        Returns:
            是否成功
        """
        import subprocess
        import tempfile
        
        try:
            # 创建临时 DOT 文件
            with tempfile.NamedTemporaryFile(mode='w', suffix='.dot', delete=False) as f:
                f.write(self.to_dot())
                dot_file = f.name
            
            # 调用 Graphviz
            cmd = ['dot', f'-T{format}', dot_file, '-o', output_file]
            result = subprocess.run(cmd, capture_output=True, text=True)
            
            # 清理临时文件
            os.unlink(dot_file)
            
            if result.returncode == 0:
                print(f"Image saved: {output_file}")
                return True
            else:
                print(f"Graphviz error: {result.stderr}")
                return False
                
        except FileNotFoundError:
            print("Error: Graphviz not found. Please install it first.")
            print("  Ubuntu/Debian: sudo apt-get install graphviz")
            print("  macOS: brew install graphviz")
            print("  Windows: choco install graphviz")
            return False
        except Exception as e:
            print(f"Error rendering image: {e}")
            return False


class AnimationSimulator:
    """
    动画模拟器 - 在控制台显示 Petri 网的动态执行
    """
    
    def __init__(self, petri_net: PetriNet, visualizer: Optional[TextVisualizer] = None):
        """
        创建动画模拟器
        
        Args:
            petri_net: 要模拟的 Petri 网
            visualizer: 可视化器（可选）
        """
        self.net = petri_net
        self.viz = visualizer or TextVisualizer(petri_net)
    
    def run_interactive(self) -> None:
        """
        交互式模拟运行
        
        提示用户输入要触发的变迁
        """
        import time
        
        print("\n" + "=" * 60)
        print("Interactive Petri Net Simulator")
        print("=" * 60)
        print("\nInitial state:")
        self.viz.print()
        
        while True:
            enabled = self.net.get_enabled_transitions()
            
            if not enabled:
                print("\n⚠️  Deadlock! No transitions are enabled.")
                break
            
            print(f"\nEnabled transitions: {', '.join(enabled)}")
            print("Enter transition to fire (or 'auto', 'quit', 'reset'):")
            
            try:
                cmd = input("> ").strip().lower()
            except (EOFError, KeyboardInterrupt):
                print("\nExiting...")
                break
            
            if cmd == 'quit' or cmd == 'q':
                break
            elif cmd == 'reset' or cmd == 'r':
                self.net.reset()
                print("\nNetwork reset.")
                self.viz.print()
            elif cmd == 'auto' or cmd == 'a':
                print("\nAuto-running...")
                self.run_auto(delay=0.5)
                break
            elif cmd in self.net.transitions:
                if self.net.fire(cmd):
                    print(f"\n✓ Fired: {cmd}")
                    self.viz.print()
                else:
                    print(f"\n✗ Cannot fire: {cmd} (not enabled)")
            else:
                print(f"\n✗ Unknown transition: {cmd}")
        
        print("\n" + "=" * 60)
        print("Final state:")
        self.viz.print()
        print("=" * 60)
    
    def run_auto(self, delay: float = 0.5, max_steps: int = 100) -> None:
        """
        自动运行模拟
        
        Args:
            delay: 每步之间的延迟（秒）
            max_steps: 最大步数
        """
        import time
        
        print("\nAuto simulation started...")
        self.viz.print()
        
        for step in range(max_steps):
            enabled = self.net.get_enabled_transitions()
            
            if not enabled:
                print(f"\n⏹️  Stopped at step {step}: Deadlock reached")
                break
            
            time.sleep(delay)
            fired = self.net.fire_any()
            
            print(f"\n{'─' * 60}")
            print(f"Step {self.net.step_count}: Fired '{fired}'")
            self.viz.print()
        
        print(f"\n{'=' * 60}")
        print("Simulation complete!")
        print(f"Total steps: {self.net.step_count}")
        print(f"Final state: {self.viz.render_compact()}")


def demo_visualization():
    """演示可视化功能"""
    from petri_net import create_sequence_net, create_fork_join_net
    
    print("=" * 70)
    print("Petri Net Visualization Demo")
    print("=" * 70)
    
    # 演示 1: 简单顺序网络
    print("\n1. Sequence Network (顺序网络)")
    print("-" * 70)
    
    seq_net = create_sequence_net(3)
    viz = TextVisualizer(seq_net)
    viz.print()
    
    print("\nRunning...")
    seq_net.run()
    viz.print()
    viz.print_history()
    
    # 演示 2: Fork-Join 网络
    print("\n" + "=" * 70)
    print("2. Fork-Join Network (并行网络)")
    print("-" * 70)
    
    fj_net = create_fork_join_net()
    viz2 = TextVisualizer(fj_net)
    
    print("Initial state:")
    viz2.print()
    
    print("\nStep-by-step execution:")
    while True:
        enabled = fj_net.get_enabled_transitions()
        if not enabled:
            break
        
        fired = fj_net.fire_any()
        print(f"\n  Fired: {fired}")
        print(f"  State: {viz2.render_compact()}")
    
    print(f"\nFinal state:")
    viz2.print()
    
    # 演示 3: DOT 格式输出
    print("\n" + "=" * 70)
    print("3. DOT Format Output")
    print("-" * 70)
    
    graph_viz = GraphVisualizer(seq_net)
    dot_output = graph_viz.to_dot()
    print(dot_output[:500] + "...\n")
    print("(Full output truncated for display)")
    
    # 保存 DOT 文件
    graph_viz.save_dot("petri_net.dot")
    print("\nTo render as image, run: dot -Tpng petri_net.dot -o petri_net.png")


if __name__ == "__main__":
    demo_visualization()
