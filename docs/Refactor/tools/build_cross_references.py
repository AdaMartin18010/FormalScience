#!/usr/bin/env python3
"""
FormalScience 文档交叉引用建立工具

功能：
1. 扫描所有文档，提取关键概念、术语、定理和代码示例
2. 建立模块间的交叉引用链接
3. 更新知识地图 (00_MAP.md)
4. 生成概念索引 (03.1_概念索引.md)
"""

import os
import re
import json
from pathlib import Path
from collections import defaultdict
from datetime import datetime

# 基础配置
DOCS_ROOT = Path("docs/Refactor")
EXCLUDE_DIRS = {'.context', '.github', '.project', '.templates', 'i18n', 'data', 'demo', 'examples', 'projects', 'tests', 'tools', 'tutorials', 'quickref', 'visual', 'benchmarks', 'cases'}
EXCLUDE_FILES = {'00_MAP.md', '00_INDEX.md', '00_PROGRESS.md', '00_GETTING_STARTED.md', '00_GLOSSARY.md', 'README.md'}

# 模块映射
MODULES = {
    '01_数学基础': 'math',
    '02_形式语言': 'formal_lang',
    '03_编程范式': 'programming',
    '04_软件工程': 'software_eng',
    '05_形式化理论': 'formal_theory',
    '06_调度系统': 'scheduling',
    '07_交叉视角': 'cross_view',
    '08_附录': 'appendix',
    '09_统计学': 'statistics',
    '10_信息论': 'information',
    '11_系统科学': 'systems',
    '12_决策与博弈论': 'decision',
    '13_认知科学形式模型': 'cognitive',
    '14_形式语言学': 'linguistics',
    '15_社会科学形式化': 'social_science'
}

# 关键概念定义
KEY_CONCEPTS = {
    # 数学基础概念
    '集合论': ('01_数学基础/01_元数学基础/01.1_集合论基础.md', '数学基础'),
    '数理逻辑': ('01_数学基础/01_元数学基础/01.2_数理逻辑.md', '数学基础'),
    '证明论': ('01_数学基础/01_元数学基础/01.3_证明论基础.md', '数学基础'),
    '递归论': ('01_数学基础/01_元数学基础/01.3_递归论与可计算性.md', '数学基础'),
    '可计算性': ('01_数学基础/01_元数学基础/01.4_可计算性理论.md', '数学基础'),
    '抽象代数': ('01_数学基础/02_代数学/02.1_抽象代数.md', '数学基础'),
    '群论': ('01_数学基础/02_代数学/02.1_群论基础.md', '数学基础'),
    '环与域': ('01_数学基础/02_代数学/02.2_环与域.md', '数学基础'),
    '线性代数': ('01_数学基础/02_代数学/02.2_线性代数.md', '数学基础'),
    '范畴论代数': ('01_数学基础/02_代数学/02.3_范畴论代数.md', '数学基础'),
    '欧几里得几何': ('01_数学基础/03_几何学/03.1_欧几里得几何.md', '数学基础'),
    '微分几何': ('01_数学基础/03_几何学/03.2_微分几何.md', '数学基础'),
    '代数拓扑': ('01_数学基础/03_几何学/03.3_代数拓扑.md', '数学基础'),
    '实分析': ('01_数学基础/04_分析学/04.1_实分析.md', '数学基础'),
    '泛函分析': ('01_数学基础/04_分析学/04.2_泛函分析.md', '数学基础'),
    '测度论': ('01_数学基础/05_概率论与测度论/05.1_测度论基础.md', '数学基础'),
    '概率论': ('01_数学基础/05_概率论与测度论/05.2_概率论基础.md', '数学基础'),
    
    # 形式语言概念
    '形式语法': ('02_形式语言/01_形式语言基础/01.1_形式语法.md', '形式语言'),
    '文法': ('02_形式语言/01_形式语言基础/01.1_文法与语言.md', '形式语言'),
    '有限自动机': ('02_形式语言/01_形式语言基础/01.2_有限自动机.md', '形式语言'),
    '形式语义': ('02_形式语言/01_形式语言基础/01.2_形式语义.md', '形式语言'),
    'λ演算': ('02_形式语言/01_形式语言基础/01.3_λ演算.md', '形式语言'),
    '下推自动机': ('02_形式语言/01_形式语言基础/01.3_下推自动机.md', '形式语言'),
    '图灵机': ('02_形式语言/01_形式语言基础/01.4_图灵机与计算.md', '形式语言'),
    '组合逻辑': ('02_形式语言/01_形式语言基础/01.4_组合逻辑.md', '形式语言'),
    '简单类型论': ('02_形式语言/02_类型论/02.1_简单类型论.md', '形式语言'),
    '多态类型': ('02_形式语言/02_类型论/02.2_多态类型论.md', '形式语言'),
    '依赖类型': ('02_形式语言/02_类型论/02.3_依赖类型论.md', '形式语言'),
    'Curry-Howard': ('02_形式语言/02_类型论/02.4_类型论与逻辑.md', '形式语言'),
    'HoTT': ('02_形式语言/03_同伦类型论_HoTT/03.1_HoTT基础.md', '形式语言'),
    '同伦类型论': ('02_形式语言/03_同伦类型论_HoTT/03.1_HoTT基础.md', '形式语言'),
    '恒等类型': ('02_形式语言/03_同伦类型论_HoTT/03.2_恒等类型.md', '形式语言'),
    '高阶归纳类型': ('02_形式语言/03_同伦类型论_HoTT/03.3_高阶归纳类型.md', '形式语言'),
    '范畴论': ('02_形式语言/04_范畴论/04.1_范畴基础.md', '形式语言'),
    '范畴基础': ('02_形式语言/04_范畴论/04.1_范畴基本概念.md', '形式语言'),
    '极限与余极限': ('02_形式语言/04_范畴论/04.2_极限与余极限.md', '形式语言'),
    '伴随与单子': ('02_形式语言/04_范畴论/04.3_伴随与单子.md', '形式语言'),
    
    # 编程范式概念
    '操作语义': ('03_编程范式/01_编程语言理论/01.1_操作语义.md', '编程范式'),
    '指称语义': ('03_编程范式/01_编程语言理论/01.2_指称语义.md', '编程范式'),
    '公理语义': ('03_编程范式/01_编程语言理论/01.3_公理语义.md', '编程范式'),
    '并发编程模型': ('03_编程范式/01_编程语言理论/01.4_并发编程模型.md', '编程范式'),
    '所有权系统': ('03_编程范式/02_Rust语言深入/02.1_所有权系统.md', '编程范式'),
    'Rust类型系统': ('03_编程范式/02_Rust语言深入/02.2_Rust类型系统.md', '编程范式'),
    'Rust错误处理': ('03_编程范式/02_Rust语言深入/02.3_Rust错误处理.md', '编程范式'),
    '内存安全形式化': ('03_编程范式/02_Rust语言深入/02.3_内存安全形式化.md', '编程范式'),
    '线性类型': ('03_编程范式/02_Rust语言深入/02.4_Rust与线性类型.md', '编程范式'),
    '异步编程': ('03_编程范式/03_异步编程模型/03.1_异步编程基础.md', '编程范式'),
    'Future与Promise': ('03_编程范式/03_异步编程模型/03.2_Future与Promise.md', '编程范式'),
    'Tokio': ('03_编程范式/03_异步编程模型/03.2_Tokio运行时.md', '编程范式'),
    '异步形式化': ('03_编程范式/03_异步编程模型/03.4_异步形式化.md', '编程范式'),
    '函数式编程': ('03_编程范式/04_函数式编程/04.1_函数式基础.md', '编程范式'),
    '高阶函数': ('03_编程范式/04_函数式编程/04.2_高阶函数.md', '编程范式'),
    '单子': ('03_编程范式/04_函数式编程/04.2_单子与函子.md', '编程范式'),
    '函子': ('03_编程范式/04_函数式编程/04.2_单子与函子.md', '编程范式'),
    '惰性求值': ('03_编程范式/04_函数式编程/04.3_惰性求值.md', '编程范式'),
    
    # 软件工程概念
    '设计模式': ('04_软件工程/01_设计模式/01.1_创建型模式.md', '软件工程'),
    '创建型模式': ('04_软件工程/01_设计模式/01.1_创建型模式.md', '软件工程'),
    '结构型模式': ('04_软件工程/01_设计模式/01.2_结构型模式.md', '软件工程'),
    '行为型模式': ('04_软件工程/01_设计模式/01.3_行为型模式.md', '软件工程'),
    '并发模式': ('04_软件工程/01_设计模式/01.4_并发模式.md', '软件工程'),
    '微服务': ('04_软件工程/02_微服务架构/02.1_微服务设计原则.md', '软件工程'),
    '服务发现': ('04_软件工程/02_微服务架构/02.2_服务发现与注册.md', '软件工程'),
    'API网关': ('04_软件工程/02_微服务架构/02.3_API网关.md', '软件工程'),
    '熔断限流': ('04_软件工程/02_微服务架构/02.3_熔断与限流.md', '软件工程'),
    '工作流': ('04_软件工程/03_工作流系统/03.1_工作流基础.md', '软件工程'),
    '分布式事务': ('04_软件工程/03_工作流系统/03.2_分布式事务.md', '软件工程'),
    '事件驱动': ('04_软件工程/03_工作流系统/03.3_事件驱动架构.md', '软件工程'),
    '一致性模型': ('04_软件工程/04_分布式系统/04.1_一致性模型.md', '软件工程'),
    '共识算法': ('04_软件工程/04_分布式系统/04.2_共识算法.md', '软件工程'),
    '分布式时钟': ('04_软件工程/04_分布式系统/04.3_分布式时钟.md', '软件工程'),
    
    # 形式化理论概念
    'LTL': ('05_形式化理论/01_时序逻辑/01.1_线性时序逻辑_LTL.md', '形式化理论'),
    '线性时序逻辑': ('05_形式化理论/01_时序逻辑/01.1_线性时序逻辑_LTL.md', '形式化理论'),
    'CTL': ('05_形式化理论/01_时序逻辑/01.2_计算树逻辑_CTL.md', '形式化理论'),
    'Petri网': ('05_形式化理论/02_Petri网理论/02.1_Petri网基础.md', '形式化理论'),
    '控制论': ('05_形式化理论/03_控制论/03.1_系统动力学.md', '形式化理论'),
    '自动机理论': ('05_形式化理论/04_计算理论/04.1_自动机理论.md', '形式化理论'),
    '计算复杂性': ('05_形式化理论/04_计算理论/04.3_计算复杂性.md', '形式化理论'),
    
    # 调度系统概念
    '调度理论': ('06_调度系统/01_调度理论基础/01.1_调度问题定义.md', '调度系统'),
    '调度复杂性': ('06_调度系统/01_调度理论基础/01.2_调度复杂性.md', '调度系统'),
    'CPU调度': ('06_调度系统/02_硬件调度/02.1_CPU调度.md', '调度系统'),
    'GPU调度': ('06_调度系统/02_硬件调度/02.2_GPU调度.md', '调度系统'),
    '进程调度': ('06_调度系统/03_OS调度/03.1_进程调度.md', '调度系统'),
    '线程调度': ('06_调度系统/03_OS调度/03.2_线程调度.md', '调度系统'),
    '集群调度': ('06_调度系统/04_分布式调度/04.1_集群调度.md', '调度系统'),
    
    # 交叉视角概念
    '形式化统一': ('07_交叉视角/01_形式化方法统一/01.1_统一理论基础.md', '交叉视角'),
    '范畴论统一': ('07_交叉视角/01_形式化方法统一/01.2_范畴论统一视角.md', '交叉视角'),
    '类型论统一': ('07_交叉视角/01_形式化方法统一/01.3_类型论统一视角.md', '交叉视角'),
    '证明与程序': ('07_交叉视角/01_形式化方法统一/01.4_证明与程序对应.md', '交叉视角'),
    '调度理论统一': ('07_交叉视角/01_形式化方法统一/01.4_调度理论统一.md', '交叉视角'),
    
    # 统计学概念
    '描述统计': ('09_统计学/01_描述统计/01.1_集中趋势与离散度.md', '统计学'),
    '概率空间': ('09_统计学/02_概率论基础/02.1_概率空间与公理.md', '统计学'),
    '随机变量': ('09_统计学/02_概率论基础/02.2_随机变量.md', '统计学'),
    '概率分布': ('09_统计学/02_概率论基础/02.3_概率分布.md', '统计学'),
    '大数定律': ('09_统计学/02_概率论基础/02.4_大数定律与中心极限定理.md', '统计学'),
    '中心极限定理': ('09_统计学/02_概率论基础/02.4_大数定律与中心极限定理.md', '统计学'),
    '点估计': ('09_统计学/03_推断统计/03.1_点估计.md', '统计学'),
    '假设检验': ('09_统计学/03_推断统计/03.3_假设检验.md', '统计学'),
    '贝叶斯统计': ('09_统计学/04_贝叶斯统计/04.1_贝叶斯定理.md', '统计学'),
    
    # 信息论概念
    '香农熵': ('10_信息论/01_香农信息论基础/01.2_熵的定义与性质.md', '信息论'),
    '信息熵': ('10_信息论/01_香农信息论基础/01.2_熵的定义与性质.md', '信息论'),
    '互信息': ('10_信息论/01_香农信息论基础/01.4_互信息与相对熵.md', '信息论'),
    '信道容量': ('10_信息论/03_信道编码/03.1_信道容量.md', '信息论'),
    'Kolmogorov复杂度': ('10_信息论/04_算法信息论/04.1_Kolmogorov复杂度.md', '信息论'),
    
    # 系统科学概念
    '系统论': ('11_系统科学/01_一般系统论/01.1_系统的概念.md', '系统科学'),
    '复杂系统': ('11_系统科学/03_复杂系统/03.1_复杂性度量.md', '系统科学'),
    '网络科学': ('11_系统科学/05_网络科学/05.1_图论基础.md', '系统科学'),
    
    # 决策与博弈论概念
    '决策理论': ('12_决策与博弈论/01_决策理论基础/01.1_偏好与效用.md', '决策与博弈论'),
    '博弈论': ('12_决策与博弈论/02_博弈论基础/02.1_博弈的表示.md', '决策与博弈论'),
    '纳什均衡': ('12_决策与博弈论/02_博弈论基础/02.2_纳什均衡.md', '决策与博弈论'),
    '机制设计': ('12_决策与博弈论/03_机制设计/03.1_显示原理.md', '决策与博弈论'),
    '社会选择': ('12_决策与博弈论/04_社会选择理论/04.1_阿罗不可能定理.md', '决策与博弈论'),
    
    # 认知科学概念
    '形式认识论': ('13_认知科学形式模型/01_形式认识论/01.1_信念的逻辑.md', '认知科学'),
    '知识逻辑': ('13_认知科学形式模型/01_形式认识论/01.2_知识逻辑.md', '认知科学'),
    '认知架构': ('13_认知科学形式模型/02_计算认知科学/02.1_认知架构_ACT-R.md', '认知科学'),
    
    # 形式语言学概念
    'Chomsky层次': ('14_形式语言学/01_形式语法/01.1_Chomsky层次.md', '形式语言学'),
    'Montague语法': ('14_形式语言学/02_形式语义学/02.1_Montague语法.md', '形式语言学'),
    '计算语言学': ('14_形式语言学/04_计算语言学/04.1_形式语言与自动机.md', '形式语言学'),
    
    # 社会科学形式化概念
    '数理经济学': ('15_社会科学形式化/01_数理经济学基础/01.1_一般均衡理论.md', '社会科学'),
    '形式政治学': ('15_社会科学形式化/02_形式政治学/02.1_投票理论.md', '社会科学'),
    '计算社会学': ('15_社会科学形式化/03_计算社会学/03.1_社会网络分析.md', '社会科学'),
}

# 定理映射
THEOREMS = {
    '施罗德-伯恩斯坦定理': ('01_数学基础/01_元数学基础/01.1_集合论基础.md#定理-1151-施罗德-伯恩斯坦定理', '集合论'),
    '良序定理': ('01_数学基础/01_元数学基础/01.1_集合论基础.md#定理-1152-良序定理', '集合论'),
    '康托尔定理': ('01_数学基础/01_元数学基础/01.1_集合论基础.md', '集合论'),
    'Church-Rosser定理': ('02_形式语言/01_形式语言基础/01.3_λ演算.md', 'λ演算'),
    '类型唯一性定理': ('02_形式语言/02_类型论/02.1_简单类型论.md', '类型论'),
    '进展性定理': ('02_形式语言/02_类型论/02.1_简单类型论.md', '类型论'),
    '类型保持定理': ('02_形式语言/02_类型论/02.1_简单类型论.md', '类型论'),
    '强正规化': ('02_形式语言/02_类型论/02.1_简单类型论.md', '类型论'),
    '阿罗不可能定理': ('12_决策与博弈论/04_社会选择理论/04.1_阿罗不可能定理.md', '社会选择'),
}

# 模块间引用关系
MODULE_CROSS_REFS = {
    '01_数学基础': [
        ('02_形式语言/02_类型论/02.1_简单类型论.md', '类型论的集合论基础'),
        ('02_形式语言/04_范畴论/04.1_范畴基础.md', '范畴论的代数基础'),
        ('05_形式化理论/04_计算理论/04.1_自动机理论.md', '自动机的数学基础'),
    ],
    '02_形式语言': [
        ('01_数学基础/01_元数学基础/01.2_数理逻辑.md', '形式语言的逻辑基础'),
        ('03_编程范式/01_编程语言理论/01.1_操作语义.md', 'PLT的形式语义基础'),
        ('03_编程范式/04_函数式编程/04.1_λ演算.md', 'λ演算的计算模型'),
    ],
    '03_编程范式': [
        ('02_形式语言/02_类型论/02.1_简单类型论.md', '类型系统理论基础'),
        ('02_形式语言/04_范畴论/04.3_伴随与单子.md', '单子的范畴论基础'),
        ('04_软件工程/01_设计模式/01.1_创建型模式.md', '设计模式的编程实现'),
    ],
    '04_软件工程': [
        ('03_编程范式/02_Rust语言深入/02.1_所有权系统.md', 'Rust的工程实践'),
        ('05_形式化理论/01_时序逻辑/01.1_线性时序逻辑_LTL.md', '协议验证理论'),
        ('05_形式化理论/02_Petri网理论/02.1_Petri网基础.md', '工作流建模理论'),
    ],
    '05_形式化理论': [
        ('01_数学基础/01_元数学基础/01.2_数理逻辑.md', '时序逻辑的逻辑基础'),
        ('02_形式语言/01_形式语言基础/01.2_有限自动机.md', '自动机理论基础'),
    ],
    '06_调度系统': [
        ('01_数学基础/04_分析学/04.1_实分析.md', '调度分析的数学工具'),
        ('05_形式化理论/03_控制论/03.1_系统动力学.md', '调度控制理论'),
        ('03_编程范式/03_异步编程模型/03.2_Tokio运行时.md', '异步调度实现'),
    ],
    '07_交叉视角': [
        ('01_数学基础/_index.md', '数学基础'),
        ('02_形式语言/_index.md', '形式语言'),
        ('03_编程范式/_index.md', '编程范式'),
        ('04_软件工程/_index.md', '软件工程'),
        ('05_形式化理论/_index.md', '形式化理论'),
        ('06_调度系统/_index.md', '调度系统'),
    ],
}


class CrossReferenceBuilder:
    """交叉引用构建器"""
    
    def __init__(self, docs_root):
        self.docs_root = Path(docs_root)
        self.all_files = []
        self.concepts_found = defaultdict(list)  # 概念 -> [(文件路径, 上下文)]
        self.links_created = 0
        self.stats = {
            'files_processed': 0,
            'concepts_linked': 0,
            'theorems_linked': 0,
            'module_refs': 0,
            'errors': []
        }
    
    def scan_all_files(self):
        """扫描所有markdown文件"""
        print("🔍 扫描文档文件...")
        for md_file in self.docs_root.rglob("*.md"):
            # 排除特定目录
            relative = md_file.relative_to(self.docs_root)
            if any(part in EXCLUDE_DIRS for part in relative.parts):
                continue
            if md_file.name in EXCLUDE_FILES:
                continue
            self.all_files.append(md_file)
        
        print(f"   找到 {len(self.all_files)} 个文档文件")
        return self.all_files
    
    def extract_concepts(self, content):
        """从内容中提取已定义的概念"""
        found = []
        for concept, (path, category) in KEY_CONCEPTS.items():
            # 检查内容中是否提到该概念（但不是在链接中）
            pattern = rf'(?<!\[)(?<!\()\b{re.escape(concept)}\b(?!\])(?!\()'
            if re.search(pattern, content):
                found.append((concept, path, category))
        return found
    
    def create_relative_link(self, from_file, to_file):
        """创建从from_file到to_file的相对路径链接"""
        from_dir = from_file.parent
        try:
            rel_path = os.path.relpath(to_file, from_dir)
            # 统一使用正斜杠
            return rel_path.replace('\\', '/')
        except ValueError:
            # Windows上不同盘符的问题
            return str(to_file.relative_to(self.docs_root)).replace('\\', '/')
    
    def process_file(self, file_path):
        """处理单个文件，添加交叉引用"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            original_content = content
            file_relative = file_path.relative_to(self.docs_root)
            module_prefix = file_relative.parts[0] if file_relative.parts else ''
            
            # 1. 添加模块间引用链接（仅在_index.md文件中）
            if file_path.name == '_index.md' and module_prefix in MODULE_CROSS_REFS:
                content = self.add_module_cross_refs(content, file_path, module_prefix)
            
            # 2. 添加概念链接
            content = self.add_concept_links(content, file_path)
            
            # 3. 添加定理引用链接
            content = self.add_theorem_links(content, file_path)
            
            # 如果内容有变化，写回文件
            if content != original_content:
                with open(file_path, 'w', encoding='utf-8') as f:
                    f.write(content)
                self.stats['files_processed'] += 1
            
            return True
            
        except Exception as e:
            self.stats['errors'].append(f"{file_path}: {str(e)}")
            return False
    
    def add_module_cross_refs(self, content, file_path, module_prefix):
        """添加模块间交叉引用"""
        if '## 🔗 相关模块链接' in content:
            return content  # 已存在
        
        cross_refs = MODULE_CROSS_REFS.get(module_prefix, [])
        if not cross_refs:
            return content
        
        # 在文件末尾添加相关模块链接
        links_section = "\n\n## 🔗 相关模块链接\n\n"
        for ref_path, description in cross_refs:
            ref_file = self.docs_root / ref_path
            if ref_file.exists():
                rel_link = self.create_relative_link(file_path, ref_file)
                links_section += f"- [{description}]({rel_link})\n"
                self.stats['module_refs'] += 1
        
        content = content.rstrip() + links_section
        return content
    
    def add_concept_links(self, content, file_path):
        """添加概念链接"""
        # 避免在已有链接中重复添加
        # 简化处理：只在明确的定义段落中添加链接
        
        for concept, target_path, category in KEY_CONCEPTS.items():
            target_file = self.docs_root / target_path
            if not target_file.exists() or target_file == file_path:
                continue
            
            # 创建相对链接
            rel_link = self.create_relative_link(file_path, target_file)
            
            # 查找概念首次出现的独立段落（不在已有链接中）
            # 匹配段落开头的概念定义
            pattern = rf'^(##+ .*?{re.escape(concept)}.*$|### 定义.*{re.escape(concept)}.*$)'
            
            def replacer(match):
                line = match.group(0)
                # 如果已经有链接，跳过
                if f'[{concept}]' in line or f']({rel_link})' in line:
                    return line
                # 在概念后添加链接
                new_line = re.sub(
                    rf'\b{re.escape(concept)}\b',
                    f'[{concept}]({rel_link})',
                    line,
                    count=1
                )
                self.stats['concepts_linked'] += 1
                return new_line
            
            content = re.sub(pattern, replacer, content, flags=re.MULTILINE)
        
        return content
    
    def add_theorem_links(self, content, file_path):
        """添加定理引用链接"""
        for theorem, (target_path, category) in THEOREMS.items():
            target_file = self.docs_root / target_path
            if not target_file.exists():
                continue
            
            rel_link = self.create_relative_link(file_path, target_file)
            
            # 匹配定理引用
            pattern = rf'\b{re.escape(theorem)}\b'
            
            if re.search(pattern, content) and f'[{theorem}]' not in content:
                content = re.sub(
                    pattern,
                    f'[{theorem}]({rel_link})',
                    content,
                    count=1
                )
                self.stats['theorems_linked'] += 1
        
        return content
    
    def update_index_files(self):
        """更新模块索引文件中的相关链接"""
        print("\n📝 更新模块索引...")
        
        for module_name, module_id in MODULES.items():
            index_file = self.docs_root / module_name / '_index.md'
            if not index_file.exists():
                continue
            
            try:
                with open(index_file, 'r', encoding='utf-8') as f:
                    content = f.read()
                
                original = content
                
                # 添加或更新相关模块链接
                if '## 🔗 相关模块链接' not in content and module_name in MODULE_CROSS_REFS:
                    content = self.add_module_cross_refs(content, index_file, module_name)
                
                if content != original:
                    with open(index_file, 'w', encoding='utf-8') as f:
                        f.write(content)
                    print(f"   更新: {index_file.relative_to(self.docs_root)}")
                    
            except Exception as e:
                self.stats['errors'].append(f"Index {index_file}: {str(e)}")
    
    def generate_concept_index(self):
        """生成概念索引文件"""
        print("\n📚 生成概念索引...")
        
        index_path = self.docs_root / '08_附录' / '03_索引' / '03.1_概念索引.md'
        index_path.parent.mkdir(parents=True, exist_ok=True)
        
        # 按拼音首字母分组
        from pypinyin import lazy_pinyin
        
        def get_pinyin(text):
            try:
                return ''.join(lazy_pinyin(text))
            except:
                return text
        
        # 构建索引内容
        content = ["# 概念索引\n", "> 按字母顺序排列的核心概念索引，包含交叉引用定位\n", "> 最后更新: {}\n".format(datetime.now().strftime('%Y-%m-%d')), ""]
        
        # 按首字母分组
        grouped = defaultdict(list)
        for concept, (path, category) in sorted(KEY_CONCEPTS.items(), key=lambda x: get_pinyin(x[0])):
            first_char = get_pinyin(concept)[0].upper()
            if not first_char.isalpha():
                first_char = '#'
            grouped[first_char].append((concept, path, category))
        
        # 生成各组内容
        for letter in sorted(grouped.keys()):
            content.append(f"\n## {letter}\n")
            content.append("| 概念 | 类别 | 文档链接 |")
            content.append("|------|------|----------|")
            
            for concept, path, category in grouped[letter]:
                doc_link = f"[{path}](../{path})"
                content.append(f"| {concept} | {category} | {doc_link} |")
        
        # 添加使用说明
        content.append("\n---\n")
        content.append("## 索引统计\n")
        content.append(f"- 总概念数: {len(KEY_CONCEPTS)}\n")
        content.append(f"- 覆盖模块: {len(set(c for _, c in KEY_CONCEPTS.values()))}\n")
        content.append("\n## 使用说明\n")
        content.append("1. 按拼音首字母快速定位概念\n")
        content.append("2. 点击文档链接跳转到详细定义\n")
        content.append("3. 类别列显示概念所属学科领域\n")
        
        # 写入文件
        with open(index_path, 'w', encoding='utf-8') as f:
            f.write('\n'.join(content))
        
        print(f"   生成: {index_path.relative_to(self.docs_root)}")
        return index_path
    
    def update_knowledge_map(self):
        """更新知识地图"""
        print("\n🗺️ 更新知识地图...")
        
        map_file = self.docs_root / '00_MAP.md'
        if not map_file.exists():
            print("   知识地图文件不存在")
            return
        
        try:
            with open(map_file, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # 添加交叉引用统计部分
            stats_section = f"""
---

## 📊 交叉引用统计

> 最后更新: {datetime.now().strftime('%Y-%m-%d')}

| 统计项 | 数量 |
|--------|------|
| 核心概念定义 | {len(KEY_CONCEPTS)} |
| 定理与引理 | {len(THEOREMS)} |
| 模块间引用关系 | {sum(len(refs) for refs in MODULE_CROSS_REFS.values())} |
| 文档文件总数 | {len(self.all_files)} |

### 概念分布

| 模块 | 概念数量 |
|------|----------|
"""
            
            # 统计各模块概念数
            module_counts = defaultdict(int)
            for _, (_, module) in KEY_CONCEPTS.items():
                module_counts[module] += 1
            
            for module, count in sorted(module_counts.items(), key=lambda x: -x[1]):
                stats_section += f"| {module} | {count} |\n"
            
            # 检查是否已存在统计部分
            if '## 📊 交叉引用统计' not in content:
                content = content.rstrip() + "\n" + stats_section
                
                with open(map_file, 'w', encoding='utf-8') as f:
                    f.write(content)
                print(f"   更新: {map_file.relative_to(self.docs_root)}")
            else:
                print("   知识地图已包含统计信息")
                
        except Exception as e:
            self.stats['errors'].append(f"Map update: {str(e)}")
    
    def run(self):
        """运行完整的交叉引用建立流程"""
        print("=" * 60)
        print("FormalScience 文档交叉引用建立工具")
        print("=" * 60)
        
        # 1. 扫描文件
        self.scan_all_files()
        
        # 2. 处理每个文件
        print("\n🔄 处理文档交叉引用...")
        for i, file_path in enumerate(self.all_files, 1):
            if i % 50 == 0:
                print(f"   进度: {i}/{len(self.all_files)}")
            self.process_file(file_path)
        
        # 3. 更新索引文件
        self.update_index_files()
        
        # 4. 生成概念索引
        self.generate_concept_index()
        
        # 5. 更新知识地图
        self.update_knowledge_map()
        
        # 6. 输出统计
        self.print_stats()
    
    def print_stats(self):
        """打印统计信息"""
        print("\n" + "=" * 60)
        print("📈 处理统计")
        print("=" * 60)
        print(f"处理的文件数: {self.stats['files_processed']}")
        print(f"概念链接数: {self.stats['concepts_linked']}")
        print(f"定理链接数: {self.stats['theorems_linked']}")
        print(f"模块引用数: {self.stats['module_refs']}")
        print(f"核心概念定义: {len(KEY_CONCEPTS)}")
        print(f"定理定义: {len(THEOREMS)}")
        
        if self.stats['errors']:
            print(f"\n⚠️ 错误数: {len(self.stats['errors'])}")
            for err in self.stats['errors'][:5]:
                print(f"   - {err}")
            if len(self.stats['errors']) > 5:
                print(f"   ... 还有 {len(self.stats['errors']) - 5} 个错误")
        
        print("\n✅ 交叉引用建立完成!")


if __name__ == '__main__':
    # 检查依赖
    try:
        import pypinyin
    except ImportError:
        print("安装依赖: pip install pypinyin")
        import subprocess
        subprocess.run(['pip', 'install', 'pypinyin'], check=True)
        import pypinyin
    
    builder = CrossReferenceBuilder(DOCS_ROOT)
    builder.run()
