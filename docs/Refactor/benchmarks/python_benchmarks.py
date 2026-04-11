#!/usr/bin/env python3
"""
FormalScience Python 工具脚本性能基准测试

测试内容：
1. 文档生成时间
2. 链接检查速度
3. 代码统计性能
4. 依赖分析性能

运行方式:
    python python_benchmarks.py
    python python_benchmarks.py --json  # 输出 JSON 格式
"""

import time
import json
import sys
import os
import re
import hashlib
from pathlib import Path
from dataclasses import dataclass, asdict
from typing import Callable, List, Dict, Any, Optional
from concurrent.futures import ThreadPoolExecutor, ProcessPoolExecutor
import argparse


# ============================================
# 基准测试框架
# ============================================

@dataclass
class BenchmarkResult:
    """基准测试结果"""
    name: str
    mean_time_ms: float
    min_time_ms: float
    max_time_ms: float
    iterations: int
    throughput: float  # ops/sec
    
    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)
    
    def print_summary(self):
        print(f"  {self.name:<30} │ 平均: {self.mean_time_ms:>8.2f}ms │ 吞吐量: {self.throughput:>10.1f} ops/sec")


class BenchmarkRunner:
    """基准测试运行器"""
    
    def __init__(self, verbose: bool = True):
        self.verbose = verbose
        self.results: List[BenchmarkResult] = []
    
    def run(self, name: str, fn: Callable[[], Any], iterations: int = 100, warmup: int = 10) -> BenchmarkResult:
        """运行单个基准测试"""
        if self.verbose:
            print(f"\n[运行] {name}...")
        
        # Warmup
        for _ in range(warmup):
            fn()
        
        # Actual timing
        times = []
        for i in range(iterations):
            start = time.perf_counter()
            fn()
            elapsed = (time.perf_counter() - start) * 1000  # ms
            times.append(elapsed)
        
        mean_time = sum(times) / len(times)
        min_time = min(times)
        max_time = max(times)
        throughput = iterations / (sum(times) / 1000)  # ops/sec
        
        result = BenchmarkResult(
            name=name,
            mean_time_ms=mean_time,
            min_time_ms=min_time,
            max_time_ms=max_time,
            iterations=iterations,
            throughput=throughput
        )
        
        self.results.append(result)
        return result
    
    def compare(self, name: str, baseline_name: str, baseline_fn: Callable, 
                candidate_name: str, candidate_fn: Callable, iterations: int = 100):
        """对比两个实现的性能"""
        print(f"\n📊 {name} 性能对比:")
        
        r1 = self.run(baseline_name, baseline_fn, iterations)
        r2 = self.run(candidate_name, candidate_fn, iterations)
        
        r1.print_summary()
        r2.print_summary()
        
        improvement = (r1.mean_time_ms - r2.mean_time_ms) / r1.mean_time_ms * 100
        if improvement > 0:
            print(f"  → {candidate_name} 比 {baseline_name} 快 {improvement:.1f}%")
        else:
            print(f"  → {candidate_name} 比 {baseline_name} 慢 {-improvement:.1f}%")
    
    def print_summary(self):
        """打印结果汇总"""
        print("\n" + "=" * 70)
        print("📋 测试结果汇总")
        print("=" * 70)
        for r in self.results:
            r.print_summary()
        print("=" * 70)


# ============================================
# 测试 1: 文档生成性能
# ============================================

class MarkdownGenerator:
    """Markdown 文档生成器"""
    
    def __init__(self):
        self.toc = []
        self.content = []
    
    def add_heading(self, level: int, text: str):
        self.content.append(f"{'#' * level} {text}\n")
        if level <= 3:
            self.toc.append(f"{'  ' * (level-1)}- [{text}](#{self._anchor(text)})")
    
    def add_paragraph(self, text: str):
        self.content.append(f"{text}\n")
    
    def add_code_block(self, code: str, lang: str = ""):
        self.content.append(f"```{lang}\n{code}\n```\n")
    
    def add_table(self, headers: List[str], rows: List[List[str]]):
        self.content.append("| " + " | ".join(headers) + " |\n")
        self.content.append("| " + " | ".join(["---"] * len(headers)) + " |\n")
        for row in rows:
            self.content.append("| " + " | ".join(row) + " |\n")
    
    def _anchor(self, text: str) -> str:
        return text.lower().replace(" ", "-").replace(".", "")
    
    def generate(self) -> str:
        return "# 目录\n\n" + "\n".join(self.toc) + "\n\n" + "".join(self.content)


def benchmark_document_generation(runner: BenchmarkRunner):
    """测试文档生成性能"""
    print("\n🔵 文档生成性能测试")
    print("=" * 70)
    
    # 测试 1: 简单文档生成
    def simple_doc():
        gen = MarkdownGenerator()
        gen.add_heading(1, "测试文档")
        gen.add_heading(2, "简介")
        gen.add_paragraph("这是一个测试段落。" * 10)
        return gen.generate()
    
    runner.run("简单文档生成", simple_doc, iterations=1000)
    
    # 测试 2: 复杂文档生成
    def complex_doc():
        gen = MarkdownGenerator()
        gen.add_heading(1, "复杂测试文档")
        
        for i in range(10):
            gen.add_heading(2, f"第{i+1}章")
            gen.add_paragraph(f"这是第{i+1}章的内容。" * 20)
            
            gen.add_heading(3, "代码示例")
            gen.add_code_block(f"def example_{i}():\n    return {i}", "python")
            
            gen.add_heading(3, "数据表格")
            gen.add_table(
                ["列A", "列B", "列C"],
                [[f"A{j}", f"B{j}", f"C{j}"] for j in range(5)]
            )
        
        return gen.generate()
    
    runner.run("复杂文档生成", complex_doc, iterations=100)
    
    # 测试 3: HTML 转换（模拟）
    sample_markdown = complex_doc()
    
    def markdown_to_html():
        """简化的 Markdown 到 HTML 转换"""
        html = sample_markdown
        # 标题转换
        for i in range(6, 0, -1):
            html = re.sub(rf'^{"#" * i} (.+)$', rf'<h{i}>\1</h{i}>', html, flags=re.MULTILINE)
        # 段落转换
        html = re.sub(r'^(?!<[h|u|o|l])(.+)$', r'<p>\1</p>', html, flags=re.MULTILINE)
        return html
    
    runner.run("Markdown转HTML", markdown_to_html, iterations=500)


# ============================================
# 测试 2: 链接检查性能
# ============================================

class LinkChecker:
    """链接检查器（模拟）"""
    
    def __init__(self):
        self.visited = set()
        self.broken = []
    
    def check_internal_link(self, link: str, base_path: str) -> bool:
        """检查内部链接"""
        if link.startswith("#"):
            return True  # 锚点链接
        
        path = Path(base_path) / link
        return path.exists()
    
    def extract_links(self, content: str) -> List[str]:
        """从 Markdown 中提取链接"""
        # 匹配 [text](url) 格式
        pattern = r'\[([^\]]+)\]\(([^)]+)\)'
        matches = re.findall(pattern, content)
        return [url for _, url in matches]
    
    def check_all_links(self, content: str, base_path: str) -> Dict[str, bool]:
        """检查所有链接"""
        links = self.extract_links(content)
        results = {}
        for link in links:
            if link.startswith("http"):
                # 外部链接 - 模拟检查
                results[link] = True
            else:
                results[link] = self.check_internal_link(link, base_path)
        return results


def benchmark_link_checking(runner: BenchmarkRunner):
    """测试链接检查性能"""
    print("\n🔵 链接检查性能测试")
    print("=" * 70)
    
    # 生成测试文档
    test_content = ""
    for i in range(100):
        test_content += f"## Section {i}\n\n"
        test_content += f"[Link to {i}](section{i}.md) "
        test_content += f"[External](https://example.com/{i}) "
        test_content += f"[Anchor](#section{i})\n\n"
    
    checker = LinkChecker()
    
    # 测试 1: 链接提取
    runner.run("链接提取", lambda: checker.extract_links(test_content), iterations=10000)
    
    # 测试 2: 完整链接检查
    runner.run("完整链接检查", 
               lambda: checker.check_all_links(test_content, "/tmp"), 
               iterations=1000)
    
    # 测试 3: 对比串行 vs 并行
    links = checker.extract_links(test_content)
    
    def serial_check():
        return [checker.check_internal_link(link, "/tmp") for link in links[:50]]
    
    def parallel_check():
        with ThreadPoolExecutor(max_workers=4) as executor:
            return list(executor.map(
                lambda l: checker.check_internal_link(l, "/tmp"), 
                links[:50]
            ))
    
    runner.compare("串行 vs 并行链接检查", "串行", serial_check, "并行", parallel_check, iterations=100)


# ============================================
# 测试 3: 代码统计性能
# ============================================

def benchmark_code_statistics(runner: BenchmarkRunner):
    """测试代码统计性能"""
    print("\n🔵 代码统计性能测试")
    print("=" * 70)
    
    # 生成测试代码
    test_code_lines = []
    for i in range(1000):
        if i % 5 == 0:
            test_code_lines.append(f"# 这是第{i}行的注释")
        elif i % 7 == 0:
            test_code_lines.append("")
        else:
            test_code_lines.append(f"def function_{i}():\n    return {i}")
    test_code = "\n".join(test_code_lines)
    
    # 测试 1: 基础统计
    def basic_stats():
        lines = test_code.split('\n')
        total = len(lines)
        non_empty = sum(1 for l in lines if l.strip())
        comments = sum(1 for l in lines if l.strip().startswith('#'))
        return {"total": total, "non_empty": non_empty, "comments": comments}
    
    runner.run("基础代码统计", basic_stats, iterations=10000)
    
    # 测试 2: 代码复杂度分析
    def complexity_analysis():
        """简化的圈复杂度计算"""
        complexity = 1
        for line in test_code.split('\n'):
            if any(kw in line for kw in ['if', 'for', 'while', 'case']):
                complexity += 1
        return complexity
    
    runner.run("圈复杂度分析", complexity_analysis, iterations=10000)
    
    # 测试 3: 文件哈希计算
    def compute_hash():
        return hashlib.sha256(test_code.encode()).hexdigest()
    
    runner.run("文件哈希计算 (SHA-256)", compute_hash, iterations=100000)
    
    # 测试 4: 正则表达式匹配统计
    pattern = re.compile(r'def\s+(\w+)\s*\(')
    
    def regex_stats():
        return len(pattern.findall(test_code))
    
    runner.run("正则函数匹配", regex_stats, iterations=10000)


# ============================================
# 测试 4: 依赖分析性能
# ============================================

def benchmark_dependency_analysis(runner: BenchmarkRunner):
    """测试依赖分析性能"""
    print("\n🔵 依赖分析性能测试")
    print("=" * 70)
    
    # 生成模拟的模块依赖图
    num_modules = 100
    dependencies = {}
    for i in range(num_modules):
        deps = [(i + j) % num_modules for j in range(1, 5)]
        dependencies[f"module_{i}"] = [f"module_{d}" for d in deps]
    
    # 测试 1: 直接依赖查找
    def find_direct_deps():
        return dependencies.get("module_50", [])
    
    runner.run("直接依赖查找", find_direct_deps, iterations=1000000)
    
    # 测试 2: 传递依赖计算（DFS）
    def transitive_deps_dfs(start: str, deps: Dict[str, List[str]]) -> set:
        visited = set()
        stack = [start]
        while stack:
            node = stack.pop()
            if node not in visited:
                visited.add(node)
                stack.extend(deps.get(node, []))
        return visited - {start}
    
    runner.run("传递依赖计算 (DFS)", 
               lambda: transitive_deps_dfs("module_0", dependencies), 
               iterations=1000)
    
    # 测试 3: 循环依赖检测
    def detect_cycles(deps: Dict[str, List[str]]) -> List[List[str]]:
        """Tarjan 算法检测强连通分量"""
        index_counter = [0]
        stack = []
        lowlinks = {}
        index = {}
        result = []
        
        def strongconnect(node):
            index[node] = index_counter[0]
            lowlinks[node] = index_counter[0]
            index_counter[0] += 1
            stack.append(node)
            
            for successor in deps.get(node, []):
                if successor not in index:
                    strongconnect(successor)
                    lowlinks[node] = min(lowlinks[node], lowlinks[successor])
                elif successor in stack:
                    lowlinks[node] = min(lowlinks[node], index[successor])
            
            if lowlinks[node] == index[node]:
                connected_component = []
                while True:
                    successor = stack.pop()
                    connected_component.append(successor)
                    if successor == node:
                        break
                if len(connected_component) > 1:
                    result.append(connected_component)
        
        for node in deps:
            if node not in index:
                strongconnect(node)
        
        return result
    
    runner.run("循环依赖检测 (Tarjan)", 
               lambda: detect_cycles(dependencies), 
               iterations=1000)
    
    # 测试 4: 依赖图序列化
    def serialize_deps():
        return json.dumps(dependencies)
    
    runner.run("依赖图序列化 (JSON)", serialize_deps, iterations=10000)


# ============================================
# 主程序入口
# ============================================

def main():
    parser = argparse.ArgumentParser(description="FormalScience Python 性能基准测试")
    parser.add_argument("--json", action="store_true", help="输出 JSON 格式结果")
    parser.add_argument("--output", type=str, help="输出文件路径")
    args = parser.parse_args()
    
    print("╔" + "═" * 69 + "╗")
    print("║" + " FormalScience Python 性能基准测试".center(68) + "║")
    print("╚" + "═" * 69 + "╝")
    
    runner = BenchmarkRunner(verbose=not args.json)
    
    # 运行所有测试
    benchmark_document_generation(runner)
    benchmark_link_checking(runner)
    benchmark_code_statistics(runner)
    benchmark_dependency_analysis(runner)
    
    # 打印汇总
    runner.print_summary()
    
    # 输出结果
    results = {
        "timestamp": time.strftime("%Y-%m-%d %H:%M:%S"),
        "total_tests": len(runner.results),
        "results": [r.to_dict() for r in runner.results]
    }
    
    if args.json:
        print(json.dumps(results, indent=2))
    
    if args.output:
        with open(args.output, 'w', encoding='utf-8') as f:
            json.dump(results, f, indent=2, ensure_ascii=False)
        print(f"\n💾 结果已保存到: {args.output}")
    
    print("\n✅ 所有基准测试完成!")


if __name__ == "__main__":
    main()
