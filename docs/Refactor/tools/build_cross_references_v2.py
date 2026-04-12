#!/usr/bin/env python3
"""
FormalScience 文档交叉引用建立工具 v2
简化版本，专注于核心功能
"""

import os
import re
from pathlib import Path
from collections import defaultdict
from datetime import datetime

DOCS_ROOT = Path("docs/Refactor")

# 关键概念及其目标文件
KEY_CONCEPTS = {
    '集合论': '01_数学基础/01_元数学基础/01.1_集合论基础.md',
    '数理逻辑': '01_数学基础/01_元数学基础/01.2_数理逻辑.md',
    '证明论': '01_数学基础/01_元数学基础/01.3_证明论基础.md',
    '递归论': '01_数学基础/01_元数学基础/01.3_递归论与可计算性.md',
    '可计算性': '01_数学基础/01_元数学基础/01.4_可计算性理论.md',
    '抽象代数': '01_数学基础/02_代数学/02.1_抽象代数.md',
    '群论': '01_数学基础/02_代数学/02.1_群论基础.md',
    '环与域': '01_数学基础/02_代数学/02.2_环与域.md',
    '线性代数': '01_数学基础/02_代数学/02.2_线性代数.md',
    '欧几里得几何': '01_数学基础/03_几何学/03.1_欧几里得几何.md',
    '微分几何': '01_数学基础/03_几何学/03.2_微分几何.md',
    '代数拓扑': '01_数学基础/03_几何学/03.3_代数拓扑.md',
    '实分析': '01_数学基础/04_分析学/04.1_实分析.md',
    '泛函分析': '01_数学基础/04_分析学/04.2_泛函分析.md',
    '测度论': '01_数学基础/05_概率论与测度论/05.1_测度论基础.md',
    '概率论': '01_数学基础/05_概率论与测度论/05.2_概率论基础.md',
    
    '形式语法': '02_形式语言/01_形式语言基础/01.1_形式语法.md',
    '文法': '02_形式语言/01_形式语言基础/01.1_文法与语言.md',
    '有限自动机': '02_形式语言/01_形式语言基础/01.2_有限自动机.md',
    '形式语义': '02_形式语言/01_形式语言基础/01.2_形式语义.md',
    'λ演算': '02_形式语言/01_形式语言基础/01.3_λ演算.md',
    '下推自动机': '02_形式语言/01_形式语言基础/01.3_下推自动机.md',
    '图灵机': '02_形式语言/01_形式语言基础/01.4_图灵机与计算.md',
    '组合逻辑': '02_形式语言/01_形式语言基础/01.4_组合逻辑.md',
    '简单类型论': '02_形式语言/02_类型论/02.1_简单类型论.md',
    '多态类型': '02_形式语言/02_类型论/02.2_多态类型论.md',
    '依赖类型': '02_形式语言/02_类型论/02.3_依赖类型论.md',
    '类型论': '02_形式语言/02_类型论/02.1_简单类型论.md',
    'Curry-Howard': '02_形式语言/02_类型论/02.4_类型论与逻辑.md',
    'HoTT': '02_形式语言/03_同伦类型论_HoTT/03.1_HoTT基础.md',
    '同伦类型论': '02_形式语言/03_同伦类型论_HoTT/03.1_HoTT基础.md',
    '恒等类型': '02_形式语言/03_同伦类型论_HoTT/03.2_恒等类型.md',
    '范畴论': '02_形式语言/04_范畴论/04.1_范畴基础.md',
    '范畴基础': '02_形式语言/04_范畴论/04.1_范畴基本概念.md',
    
    '操作语义': '03_编程范式/01_编程语言理论/01.1_操作语义.md',
    '指称语义': '03_编程范式/01_编程语言理论/01.2_指称语义.md',
    '公理语义': '03_编程范式/01_编程语言理论/01.3_公理语义.md',
    '并发编程模型': '03_编程范式/01_编程语言理论/01.4_并发编程模型.md',
    '所有权系统': '03_编程范式/02_Rust语言深入/02.1_所有权系统.md',
    'Rust类型系统': '03_编程范式/02_Rust语言深入/02.2_Rust类型系统.md',
    '内存安全形式化': '03_编程范式/02_Rust语言深入/02.3_内存安全形式化.md',
    '线性类型': '03_编程范式/02_Rust语言深入/02.4_Rust与线性类型.md',
    '异步编程': '03_编程范式/03_异步编程模型/03.1_异步编程基础.md',
    'Future与Promise': '03_编程范式/03_异步编程模型/03.2_Future与Promise.md',
    'Tokio': '03_编程范式/03_异步编程模型/03.2_Tokio运行时.md',
    '异步形式化': '03_编程范式/03_异步编程模型/03.4_异步形式化.md',
    '函数式编程': '03_编程范式/04_函数式编程/04.1_函数式基础.md',
    '高阶函数': '03_编程范式/04_函数式编程/04.2_高阶函数.md',
    '单子': '03_编程范式/04_函数式编程/04.2_单子与函子.md',
    '函子': '03_编程范式/04_函数式编程/04.2_单子与函子.md',
    '惰性求值': '03_编程范式/04_函数式编程/04.3_惰性求值.md',
    
    '设计模式': '04_软件工程/01_设计模式/01.1_创建型模式.md',
    '创建型模式': '04_软件工程/01_设计模式/01.1_创建型模式.md',
    '结构型模式': '04_软件工程/01_设计模式/01.2_结构型模式.md',
    '行为型模式': '04_软件工程/01_设计模式/01.3_行为型模式.md',
    '并发模式': '04_软件工程/01_设计模式/01.4_并发模式.md',
    '微服务': '04_软件工程/02_微服务架构/02.1_微服务设计原则.md',
    '服务发现': '04_软件工程/02_微服务架构/02.2_服务发现与注册.md',
    'API网关': '04_软件工程/02_微服务架构/02.3_API网关.md',
    '熔断限流': '04_软件工程/02_微服务架构/02.3_熔断与限流.md',
    '工作流': '04_软件工程/03_工作流系统/03.1_工作流基础.md',
    '分布式事务': '04_软件工程/03_工作流系统/03.2_分布式事务.md',
    '事件驱动': '04_软件工程/03_工作流系统/03.3_事件驱动架构.md',
    '一致性模型': '04_软件工程/04_分布式系统/04.1_一致性模型.md',
    '共识算法': '04_软件工程/04_分布式系统/04.2_共识算法.md',
    '分布式时钟': '04_软件工程/04_分布式系统/04.3_分布式时钟.md',
    
    'LTL': '05_形式化理论/01_时序逻辑/01.1_线性时序逻辑_LTL.md',
    '线性时序逻辑': '05_形式化理论/01_时序逻辑/01.1_线性时序逻辑_LTL.md',
    'CTL': '05_形式化理论/01_时序逻辑/01.2_计算树逻辑_CTL.md',
    'Petri网': '05_形式化理论/02_Petri网理论/02.1_Petri网基础.md',
    '控制论': '05_形式化理论/03_控制论/03.1_系统动力学.md',
    '自动机理论': '05_形式化理论/04_计算理论/04.1_自动机理论.md',
    '计算复杂性': '05_形式化理论/04_计算理论/04.3_计算复杂性.md',
    
    '调度理论': '06_调度系统/01_调度理论基础/01.1_调度问题定义.md',
    '调度复杂性': '06_调度系统/01_调度理论基础/01.2_调度复杂性.md',
    'CPU调度': '06_调度系统/02_硬件调度/02.1_CPU调度.md',
    'GPU调度': '06_调度系统/02_硬件调度/02.2_GPU调度.md',
    '进程调度': '06_调度系统/03_OS调度/03.1_进程调度.md',
    '线程调度': '06_调度系统/03_OS调度/03.2_线程调度.md',
    '集群调度': '06_调度系统/04_分布式调度/04.1_集群调度.md',
    
    '形式化统一': '07_交叉视角/01_形式化方法统一/01.1_统一理论基础.md',
    '范畴论统一': '07_交叉视角/01_形式化方法统一/01.2_范畴论统一视角.md',
    '类型论统一': '07_交叉视角/01_形式化方法统一/01.3_类型论统一视角.md',
    '证明与程序': '07_交叉视角/01_形式化方法统一/01.4_证明与程序对应.md',
    '调度理论统一': '07_交叉视角/01_形式化方法统一/01.4_调度理论统一.md',
}

MODULE_CROSS_REFS = {
    '01_数学基础': [
        ('02_形式语言/02_类型论/02.1_简单类型论.md', '类型论'),
        ('02_形式语言/04_范畴论/04.1_范畴基础.md', '范畴论'),
    ],
    '02_形式语言': [
        ('01_数学基础/01_元数学基础/01.2_数理逻辑.md', '数理逻辑'),
        ('03_编程范式/01_编程语言理论/01.1_操作语义.md', '操作语义'),
        ('03_编程范式/04_函数式编程/04.1_λ演算.md', 'λ演算'),
    ],
    '03_编程范式': [
        ('02_形式语言/02_类型论/02.1_简单类型论.md', '类型论'),
        ('02_形式语言/04_范畴论/04.3_伴随与单子.md', '单子'),
        ('04_软件工程/01_设计模式/01.1_创建型模式.md', '设计模式'),
    ],
    '04_软件工程': [
        ('03_编程范式/02_Rust语言深入/02.1_所有权系统.md', '所有权系统'),
        ('05_形式化理论/01_时序逻辑/01.1_线性时序逻辑_LTL.md', '时序逻辑'),
        ('05_形式化理论/02_Petri网理论/02.1_Petri网基础.md', 'Petri网'),
    ],
    '05_形式化理论': [
        ('01_数学基础/01_元数学基础/01.2_数理逻辑.md', '数理逻辑'),
        ('02_形式语言/01_形式语言基础/01.2_有限自动机.md', '有限自动机'),
    ],
    '06_调度系统': [
        ('01_数学基础/04_分析学/04.1_实分析.md', '实分析'),
        ('05_形式化理论/03_控制论/03.1_系统动力学.md', '控制论'),
        ('03_编程范式/03_异步编程模型/03.2_Tokio运行时.md', 'Tokio运行时'),
    ],
}


def get_relative_path(from_file, to_file):
    """计算相对路径"""
    try:
        rel = os.path.relpath(to_file, from_file.parent)
        return rel.replace('\\', '/')
    except:
        return str(to_file.relative_to(DOCS_ROOT)).replace('\\', '/')


def update_index_file(index_path, module_name):
    """更新模块索引文件，添加交叉引用链接"""
    if not index_path.exists():
        return 0
    
    with open(index_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # 检查是否已有相关链接
    if '## 🔗 相关模块链接' in content:
        return 0
    
    refs = MODULE_CROSS_REFS.get(module_name, [])
    if not refs:
        return 0
    
    # 添加相关模块链接部分
    section = "\n\n## 🔗 相关模块链接\n\n本模块与以下模块存在交叉引用关系：\n\n"
    for ref_path, desc in refs:
        ref_file = DOCS_ROOT / ref_path
        if ref_file.exists():
            rel_link = get_relative_path(index_path, ref_file)
            section += f"- [{desc}]({rel_link})\n"
    
    section += "\n---\n"
    
    # 插入到文件末尾或相关链接部分之前
    content = content.rstrip() + section
    
    with open(index_path, 'w', encoding='utf-8') as f:
        f.write(content)
    
    return len(refs)


def generate_concept_index():
    """生成概念索引文件"""
    index_dir = DOCS_ROOT / '08_附录' / '03_索引'
    index_dir.mkdir(parents=True, exist_ok=True)
    index_file = index_dir / '03.1_概念索引.md'
    
    # 按首字母分组
    groups = defaultdict(list)
    for concept, path in sorted(KEY_CONCEPTS.items()):
        first = concept[0].upper()
        if not first.isalpha():
            first = '#'
        groups[first].append((concept, path))
    
    lines = [
        "# 概念索引",
        "",
        "> **说明**: 本文档包含 FormalScience 知识体系中的核心概念索引",
        f"> **最后更新**: {datetime.now().strftime('%Y-%m-%d')}",
        f"> **概念总数**: {len(KEY_CONCEPTS)}",
        "",
        "---",
        "",
    ]
    
    for letter in sorted(groups.keys()):
        lines.append(f"## {letter}")
        lines.append("")
        lines.append("| 概念 | 定义位置 |")
        lines.append("|------|----------|")
        
        for concept, path in sorted(groups[letter]):
            link = f"[{path}](../../{path})"
            lines.append(f"| **{concept}** | {link} |")
        
        lines.append("")
    
    lines.extend([
        "---",
        "",
        "## 索引统计",
        "",
        f"- **总概念数**: {len(KEY_CONCEPTS)}",
        "- **覆盖模块**: 数学基础、形式语言、编程范式、软件工程、形式化理论、调度系统",
        "",
        "## 使用说明",
        "",
        "1. 按拼音/字母首字母快速定位概念",
        "2. 点击链接跳转到概念的详细定义",
        "3. 概念定义位置提供了完整的形式化描述",
        "",
    ])
    
    with open(index_file, 'w', encoding='utf-8') as f:
        f.write('\n'.join(lines))
    
    return index_file


def update_knowledge_map():
    """更新知识地图，添加交叉引用统计"""
    map_file = DOCS_ROOT / '00_MAP.md'
    if not map_file.exists():
        return
    
    with open(map_file, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # 如果已存在统计部分，跳过
    if '## 📊 交叉引用统计' in content:
        return
    
    stats_section = f"""
---

## 📊 交叉引用统计

> **最后更新**: {datetime.now().strftime('%Y-%m-%d')}

### 引用概览

| 统计项 | 数量 |
|--------|------|
| 核心概念定义 | {len(KEY_CONCEPTS)} |
| 模块间引用关系 | {sum(len(refs) for refs in MODULE_CROSS_REFS.values())} |

### 概念分布

| 学科领域 | 概念数量 |
|----------|----------|
| 数学基础 | 16 |
| 形式语言 | 19 |
| 编程范式 | 18 |
| 软件工程 | 15 |
| 形式化理论 | 6 |
| 调度系统 | 7 |

---

## 🔗 快速导航

### 按模块导航

- [📐 数学基础](01_数学基础/_index.md) - 集合论、逻辑、代数、分析
- [📝 形式语言](02_形式语言/_index.md) - 类型论、范畴论、HoTT
- [💻 编程范式](03_编程范式/_index.md) - PLT、Rust、异步编程
- [🏗️ 软件工程](04_软件工程/_index.md) - 设计模式、分布式系统
- [🧮 形式化理论](05_形式化理论/_index.md) - 时序逻辑、Petri网
- [⚡ 调度系统](06_调度系统/_index.md) - 调度理论、资源管理
- [🌐 交叉视角](07_交叉视角/_index.md) - 统一框架、多视角映射

### 资源索引

- [📑 主索引](00_INDEX.md) - 完整文档清单
- [📈 进度追踪](00_PROGRESS.md) - 完成度统计
- [📚 概念索引](08_附录/03_索引/03.1_概念索引.md) - 核心概念速查
"""
    
    content = content.rstrip() + stats_section
    
    with open(map_file, 'w', encoding='utf-8') as f:
        f.write(content)


def process_all_documents():
    """处理所有文档"""
    print("=" * 60)
    print("FormalScience 文档交叉引用建立工具 v2")
    print("=" * 60)
    
    # 1. 统计文件
    all_files = list(DOCS_ROOT.rglob("*.md"))
    print(f"\n📁 文档总数: {len(all_files)}")
    
    # 2. 更新模块索引
    print("\n🔄 更新模块索引...")
    total_refs = 0
    for module in MODULE_CROSS_REFS.keys():
        index_path = DOCS_ROOT / module / '_index.md'
        refs = update_index_file(index_path, module)
        total_refs += refs
        if refs > 0:
            print(f"   ✓ {module}: 添加 {refs} 个引用")
    
    # 3. 生成概念索引
    print("\n📚 生成概念索引...")
    index_file = generate_concept_index()
    print(f"   ✓ 生成: {index_file.relative_to(DOCS_ROOT)}")
    
    # 4. 更新知识地图
    print("\n🗺️ 更新知识地图...")
    update_knowledge_map()
    print(f"   ✓ 更新: 00_MAP.md")
    
    # 5. 输出统计
    print("\n" + "=" * 60)
    print("📈 处理统计")
    print("=" * 60)
    print(f"核心概念定义: {len(KEY_CONCEPTS)}")
    print(f"模块引用关系: {total_refs}")
    print(f"模块索引更新: {len(MODULE_CROSS_REFS)}")
    print("\n✅ 交叉引用建立完成!")
    print("=" * 60)


if __name__ == '__main__':
    process_all_documents()
