#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FormalScience 文档摘要生成器

为 docs/Refactor/ 目录下的所有主要文档生成内容摘要。

用法:
    python generate_document_summaries.py [--dry-run] [--index-only]

选项:
    --dry-run      只显示将要修改的文件，不实际修改
    --index-only   只生成摘要索引，不修改文档
"""

import os
import re
import sys
import json
from pathlib import Path
from datetime import datetime
from dataclasses import dataclass, asdict
from typing import List, Optional, Tuple

# 项目根目录
PROJECT_ROOT = Path("e:/_src/FormalScience")
DOCS_DIR = PROJECT_ROOT / "docs/Refactor"

# 需要排除的目录模式
EXCLUDE_PATTERNS = [
    ".context",
    ".github", 
    ".project",
    ".templates",
    ".scripts",
    "assets",
    "data",
    "demo",
    "i18n",
    "benchmarks",
    "cases",
    "examples",
    "exercises",
    "projects",
    "quickref",
    "tests",
    "tools",
    "tutorials",
    "visual",
    "website",
]

# 需要排除的文件模式
EXCLUDE_FILES = [
    "00_INDEX.md",
    "00_MAP.md", 
    "00_PROGRESS.md",
    "00_GETTING_STARTED.md",
    "00_GLOSSARY.md",
    "README.md",
    "_index.md",
    "INDEX.md",
    "TASK_COMPLETION_REPORT.md",
    "99_*.md",
    "100_*.md",
    "ACKNOWLEDGMENTS.md",
    "ARCHITECTURE.md",
    "BADGES.md",
    "CHANGELOG*.md",
    "CODE_OF_CONDUCT.md",
    "COMPLIANCE.md",
    "COMPLETION*.md",
    "CONTENT_GAP_ANALYSIS.md",
    "CONTRIBUTING.md",
    "CONTRIBUTORS.md",
    "CROSS_REFERENCE_REPORT.md",
    "DEPRECATIONS.md",
    "FAQ.md",
    "FEATURE_REQUESTS.md",
    "FINAL*.md",
    "GLOSSARY*.md",
    "LICENSE.md",
    "MILESTONES.md",
    "PRIVACY.md",
    "QUICK_REFERENCE.md",
    "RELEASE_NOTES.md",
    "RESOURCES.md",
    "ROADMAP.md",
    "SECURITY.md",
    "STATUS.md",
    "SUPPORTERS.md",
    "TODO.md",
    "TROUBLESHOOTING.md",
    "VERSION*.md",
]


@dataclass
class DocumentSummary:
    """文档摘要数据结构"""
    path: str
    title: str
    summary: str
    keywords: List[str]
    learning_goals: List[str]
    difficulty: str  # 初级/中级/高级
    read_time: str   # 预计阅读时间
    prerequisites: List[str]
    category: str    # 所属类别


# 类别映射配置
CATEGORY_MAP = {
    "01_数学基础": "数学基础",
    "01_元数学基础": "元数学",
    "02_代数学": "代数学", 
    "03_几何学": "几何学",
    "04_分析学": "分析学",
    "05_概率论与测度论": "概率论与测度论",
    
    "02_形式语言": "形式语言",
    "01_形式语言基础": "形式语言基础",
    "02_类型论": "类型论",
    "03_同伦类型论_HoTT": "同伦类型论",
    "04_范畴论": "范畴论",
    
    "03_编程范式": "编程范式",
    "01_编程语言理论": "编程语言理论",
    "02_Rust语言深入": "Rust语言",
    "03_异步编程模型": "异步编程",
    "04_函数式编程": "函数式编程",
    
    "04_软件工程": "软件工程",
    "01_设计模式": "设计模式",
    "02_微服务架构": "微服务架构",
    "03_工作流系统": "工作流系统",
    "04_分布式系统": "分布式系统",
    
    "05_形式化理论": "形式化理论",
    "01_时序逻辑": "时序逻辑",
    "02_Petri网理论": "Petri网理论",
    "03_控制论": "控制论",
    "04_计算理论": "计算理论",
    
    "06_调度系统": "调度系统",
    "01_调度理论基础": "调度理论基础",
    "02_硬件调度": "硬件调度",
    "03_OS调度": "OS调度",
    "04_分布式调度": "分布式调度",
    "05_形式化证明": "调度形式化证明",
    
    "07_交叉视角": "交叉视角",
    "01_形式化方法统一": "形式化方法统一",
    "02_多视角映射": "多视角映射",
    
    "08_附录": "附录",
    "01_参考文献": "参考文献",
    "02_符号表": "符号表",
    "03_索引": "索引",
    
    "09_统计学": "统计学",
    "01_描述统计": "描述统计",
    "02_概率论基础": "概率论基础",
    "03_推断统计": "推断统计",
    "04_贝叶斯统计": "贝叶斯统计",
    "05_数理统计": "数理统计",
    "06_统计计算": "统计计算",
    
    "10_信息论": "信息论",
    "01_香农信息论基础": "香农信息论",
    "02_信源编码": "信源编码",
    "03_信道编码": "信道编码",
    "04_算法信息论": "算法信息论",
    "05_量子信息论": "量子信息论",
    
    "11_系统科学": "系统科学",
    "01_一般系统论": "一般系统论",
    "02_控制论": "控制论",
    "03_复杂系统": "复杂系统",
    "04_自组织理论": "自组织理论",
    "05_网络科学": "网络科学",
    "06_系统动力学": "系统动力学",
    
    "12_决策与博弈论": "决策与博弈论",
    "01_决策理论基础": "决策理论",
    "02_博弈论基础": "博弈论基础",
    "03_机制设计": "机制设计",
    "04_社会选择理论": "社会选择理论",
    "05_行为博弈论": "行为博弈论",
    
    "13_认知科学形式模型": "认知科学",
    "01_形式认识论": "形式认识论",
    "02_计算认知科学": "计算认知科学",
    "03_概念与范畴": "概念与范畴",
    "04_推理与问题解决": "推理与问题解决",
    "05_学习与记忆": "学习与记忆",
    
    "14_形式语言学": "形式语言学",
    "01_形式语法": "形式语法",
    "02_形式语义学": "形式语义学",
    "03_音系学形式理论": "音系学形式理论",
    "04_计算语言学": "计算语言学",
    
    "15_社会科学形式化": "社会科学形式化",
    "01_数理经济学基础": "数理经济学",
    "02_形式政治学": "形式政治学",
    "03_计算社会学": "计算社会学",
    "04_形式人类学": "形式人类学",
}


# 难度级别映射（基于路径和文件名判断）
def get_difficulty_level(rel_path: str, title: str) -> str:
    """根据路径和标题判断难度级别"""
    # 高级标志
    advanced_markers = [
        "形式化", "证明", "定理", "公理", "同伦", "HoTT",
        "复杂", "高级", "进阶", "深入", "形式化证明",
        "05.", "04.", "03.4", "02.4",
    ]
    # 初级标志  
    beginner_markers = [
        "基础", "入门", "简介", "概述", "初步",
        "01.1", "01.2", "02.1",
    ]
    
    path_and_title = rel_path.lower() + title.lower()
    
    for marker in advanced_markers:
        if marker.lower() in path_and_title:
            return "高级"
    
    for marker in beginner_markers:
        if marker.lower() in path_and_title:
            return "初级"
    
    return "中级"


# 预计阅读时间估算（基于文件大小和复杂度）
def estimate_read_time(file_size: int, complexity: str) -> str:
    """估算阅读时间"""
    base_time = file_size / 2000  # 每2000字节约1分钟
    
    if complexity == "高级":
        multiplier = 1.5
    elif complexity == "初级":
        multiplier = 0.8
    else:
        multiplier = 1.0
    
    minutes = int(base_time * multiplier)
    minutes = max(15, min(minutes, 120))  # 限制在15-120分钟
    
    # 取整到5的倍数
    minutes = ((minutes + 4) // 5) * 5
    
    return f"{minutes}分钟"


# 关键词生成映射
KEYWORD_TEMPLATES = {
    # 数学基础
    "集合论": ["集合论", "ZFC公理", "序数", "基数", "无穷集合"],
    "数理逻辑": ["数理逻辑", "命题逻辑", "谓词逻辑", "模型论", "哥德尔定理"],
    "证明论": ["证明论", "自然演绎", "相继式", "证明归约", "构造主义"],
    "递归论": ["递归论", "可计算性", "图灵机", "停机问题", "递归函数"],
    "抽象代数": ["抽象代数", "群论", "环论", "域论", "代数结构"],
    "线性代数": ["线性代数", "向量空间", "矩阵", "特征值", "张量"],
    "范畴论": ["范畴论", "函子", "自然变换", "伴随", "单子"],
    "欧几里得几何": ["欧几里得几何", "公理化", "希尔伯特", "几何变换"],
    "微分几何": ["微分几何", "流形", "黎曼度量", "曲率", "张量分析"],
    "代数拓扑": ["代数拓扑", "同调群", "上同调", "纤维丛", "同伦"],
    "实分析": ["实分析", "Lebesgue积分", "测度论", "收敛定理", "Lp空间"],
    "复分析": ["复分析", "全纯函数", "留数定理", "共形映射", "解析延拓"],
    "泛函分析": ["泛函分析", "Banach空间", "Hilbert空间", "算子理论", "谱理论"],
    "测度论": ["测度论", "σ-代数", "可测函数", "积分理论", "概率测度"],
    "概率论": ["概率论", "随机变量", "概率分布", "大数定律", "中心极限定理"],
    "随机过程": ["随机过程", "Markov链", "鞅", "布朗运动", "随机微分方程"],
    
    # 形式语言
    "形式语法": ["形式语法", "形式文法", "Chomsky层次", "上下文无关", "自动机"],
    "形式语义": ["形式语义", "操作语义", "指称语义", "公理语义", "语义等价"],
    "有限自动机": ["有限自动机", "DFA", "NFA", "正则语言", "状态转换"],
    "下推自动机": ["下推自动机", "PDA", "上下文无关", "栈", "语法分析"],
    "图灵机": ["图灵机", "可计算性", "复杂性", "P vs NP", "停机问题"],
    "λ演算": ["λ演算", "函数式", "归约", "Church-Rosser", "不动点"],
    "类型系统": ["类型系统", "类型论", "类型推断", "多态", "依赖类型"],
    "简单类型": ["简单类型", "λ演算", "类型安全", "类型推断", "Curry-Howard"],
    "多态类型": ["多态类型", "System F", "类型抽象", "泛型", "参数多态"],
    "依赖类型": ["依赖类型", "Π类型", "Σ类型", "类型族", "归纳类型"],
    "HoTT": ["同伦类型论", "HoTT", "恒等类型", "高阶归纳", "单值性"],
    "范畴": ["范畴论", "范畴", "函子", "极限", "伴随"],
    
    # 编程范式
    "操作语义": ["操作语义", "小步语义", "大步语义", "求值", "状态转换"],
    "指称语义": ["指称语义", "域论", "不动点", "连续函数", "数学语义"],
    "公理语义": ["公理语义", "Hoare逻辑", "最弱前置条件", "程序验证", "不变式"],
    "所有权": ["所有权", "Rust", "借用检查", "生命周期", "内存安全"],
    "内存安全": ["内存安全", "Rust", "形式化验证", "所有权", "线性类型"],
    "异步编程": ["异步编程", "Future", "Promise", "并发", "Tokio"],
    "函数式": ["函数式编程", "高阶函数", "纯函数", "不可变性", "单子"],
    "并发": ["并发编程", "并行", "同步", "竞态条件", "死锁"],
    
    # 软件工程
    "设计模式": ["设计模式", "创建型", "结构型", "行为型", "GoF"],
    "微服务": ["微服务", "分布式", "服务发现", "API网关", "熔断"],
    "工作流": ["工作流", "BPMN", "编排", "事务", "长时间运行"],
    "分布式": ["分布式系统", "一致性", "共识算法", "CAP定理", "分区"],
    "一致性": ["一致性模型", "强一致性", "最终一致性", "线性一致性", "因果一致性"],
    "共识": ["共识算法", "Paxos", "Raft", "PBFT", "拜占庭容错"],
    
    # 形式化理论
    "时序逻辑": ["时序逻辑", "LTL", "CTL", "模型检测", "规约"],
    "Petri网": ["Petri网", "并发", "位置", "变迁", "可达性"],
    "控制论": ["控制论", "反馈", "稳定性", "系统动力学", "最优控制"],
    "计算理论": ["计算理论", "自动机", "可计算性", "复杂性", "图灵机"],
    
    # 调度系统
    "调度": ["调度", "任务调度", "资源分配", "优化", "算法"],
    "进程调度": ["进程调度", "CPU调度", "调度算法", "优先级", "时间片"],
    "实时调度": ["实时调度", "截止时间", "EDF", "Rate Monotonic", "可调度性"],
    "集群调度": ["集群调度", "资源管理", "YARN", "Mesos", "Kubernetes"],
    
    # 统计学
    "描述统计": ["描述统计", "集中趋势", "离散度", "可视化", "EDA"],
    "推断统计": ["推断统计", "估计", "假设检验", "置信区间", "显著性"],
    "贝叶斯": ["贝叶斯统计", "先验", "后验", "贝叶斯推断", "MCMC"],
    
    # 信息论
    "信息论": ["信息论", "熵", "互信息", "信道容量", "编码"],
    "信源编码": ["信源编码", "Huffman", "算术编码", "无损压缩", "Kraft不等式"],
    "信道编码": ["信道编码", "纠错码", "汉明码", "线性分组码", "容量"],
    
    # 系统科学
    "系统论": ["系统论", "涌现", "层次", "自组织", "复杂性"],
    "复杂系统": ["复杂系统", "相变", "临界现象", "分形", "幂律"],
    "网络科学": ["网络科学", "复杂网络", "小世界", "无标度", "中心性"],
    
    # 决策与博弈
    "决策": ["决策理论", "效用", "风险", "不确定性", "期望效用"],
    "博弈论": ["博弈论", "纳什均衡", "博弈表示", "均衡概念", "策略"],
    "机制设计": ["机制设计", "显示原理", "拍卖", "激励相容", "社会选择"],
    
    # 认知科学
    "认知": ["认知科学", "形式认识论", "知识逻辑", "信念", "推理"],
    
    # 形式语言学
    "形式语言学": ["形式语言学", "Chomsky", "Montague", "语法", "语义"],
    
    # 社会科学
    "经济学": ["数理经济学", "均衡", "博弈", "信息", "机制"],
    "政治学": ["形式政治学", "投票", "权力指数", "联盟", "社会选择"],
}


def extract_title(content: str) -> str:
    """从文档内容中提取标题，并清理编号前缀"""
    lines = content.split('\n')
    for line in lines[:10]:  # 检查前10行
        line = line.strip()
        if line.startswith('# ') and not line.startswith('##'):
            title = line[2:].strip()
            # 清理编号前缀 (如 "01.1 ", "9.1.1 ", "1.1 " 等)
            title = re.sub(r'^[\d.]+\s+', '', title)
            # 清理英文副标题中的括号内容（保留中文标题）
            title = re.sub(r'\s*\([^)]*\)$', '', title)
            return title
    return "未知标题"


def generate_keywords(title: str, category: str, content_preview: str) -> List[str]:
    """根据标题、类别和内容生成关键词"""
    keywords = set()
    
    # 根据标题匹配关键词模板
    for key, words in KEYWORD_TEMPLATES.items():
        if key in title or key in content_preview[:500]:
            keywords.update(words[:3])  # 每个模板最多取3个
    
    # 添加类别关键词
    if category:
        keywords.add(category)
    
    # 如果没有匹配到，使用通用关键词
    if not keywords:
        # 从标题中提取关键词
        keywords = set(title.replace("基础", "").replace("理论", "").split())
        keywords = {k for k in keywords if len(k) > 1}
    
    # 限制数量
    return list(keywords)[:8]


def generate_learning_goals(title: str, keywords: List[str], difficulty: str) -> List[str]:
    """生成学习目标"""
    goals = []
    # 清理标题用于描述
    clean_title = title.replace('基础', '').replace('理论', '').strip()
    
    # 基础目标
    if difficulty == "初级":
        goals.append(f"理解{clean_title}的基本概念和核心原理")
        goals.append("掌握相关术语和符号表示")
    elif difficulty == "高级":
        goals.append(f"深入理解{clean_title}的理论体系和形式化方法")
        goals.append("能够进行相关定理的形式化证明")
    else:
        goals.append(f"掌握{clean_title}的核心概念和主要方法")
        goals.append("理解相关理论的应用场景")
    
    # 根据关键词添加具体目标
    if "算法" in keywords or "调度" in title:
        goals.append("能够分析和实现相关算法")
    if "证明" in title or "形式化" in title:
        goals.append("掌握形式化证明的基本技巧")
    if "应用" in title:
        goals.append("了解在实际系统中的应用场景")
    
    # 确保有3-4个目标
    if len(goals) < 3:
        goals.append("建立该领域的系统性知识框架")
    
    return goals[:4]


def generate_summary(title: str, category: str, keywords: List[str], difficulty: str) -> str:
    """生成内容摘要"""
    parts = []
    
    # 开头句
    if "基础" in title or "入门" in title:
        parts.append(f"本文档系统介绍{title.replace('基础', '').replace('入门', '')}的基础理论和核心概念。")
    elif "证明" in title or "定理" in title:
        parts.append(f"本文档提供{title}的严格形式化证明和推导过程。")
    else:
        parts.append(f"本文档深入探讨{title}的核心原理和关键方法。")
    
    # 内容范围
    if category:
        parts.append(f"内容涵盖{category}领域的主要知识点，包括")
        
        # 添加关键词作为内容要点
        key_points = [k for k in keywords[:5] if k != category]
        if key_points:
            parts.append(f"{', '.join(key_points)}等关键主题。")
        else:
            parts.append("相关理论、方法及应用。")
    
    # 学习目标
    if difficulty == "初级":
        parts.append("适合初学者建立基础知识体系。")
    elif difficulty == "高级":
        parts.append("适合具备相关基础的学习者进行深入研究。")
    else:
        parts.append("适合有一定基础的学习者系统学习。")
    
    return "".join(parts)


def generate_prerequisites(rel_path: str, difficulty: str) -> List[str]:
    """生成前置知识要求"""
    prereqs = []
    
    # 根据难度级别
    if difficulty == "初级":
        prereqs.append("基础数学知识")
    elif difficulty == "中级":
        prereqs.append("相关领域的基础概念")
    else:
        prereqs.append("该领域的中级知识")
        prereqs.append("形式化方法基础")
    
    # 根据路径判断特定前置知识
    path_lower = rel_path.lower()
    if "调度" in path_lower:
        prereqs.append("算法与数据结构")
    if "形式语言" in path_lower or "类型论" in path_lower:
        prereqs.append("离散数学")
    if "概率" in path_lower or "统计" in path_lower:
        prereqs.append("微积分基础")
    
    return prereqs[:3]


def create_summary_block(summary: DocumentSummary) -> str:
    """创建摘要区块"""
    lines = [
        "---",
        "",
        "📌 **内容摘要**",
        "",
        summary.summary,
        "",
        f"**关键词**: {', '.join(summary.keywords)}",
        "",
        "📚 **学习目标**",
    ]
    
    for goal in summary.learning_goals:
        lines.append(f"- {goal}")
    
    lines.extend([
        "",
        f"🎯 **难度级别**: {summary.difficulty}",
        "",
        f"⏱️ **预计阅读时间**: {summary.read_time}",
        "",
        f"**前置知识**: {', '.join(summary.prerequisites)}",
        "",
        "---",
        "",
    ])
    
    return '\n'.join(lines)


def should_process_file(rel_path: str) -> bool:
    """判断文件是否需要处理"""
    # 检查排除目录
    for pattern in EXCLUDE_PATTERNS:
        if pattern in rel_path:
            return False
    
    # 检查排除文件
    basename = os.path.basename(rel_path)
    for pattern in EXCLUDE_FILES:
        if pattern.endswith('*.md'):
            prefix = pattern.replace('*.md', '')
            if basename.startswith(prefix):
                return False
        elif basename == pattern:
            return False
    
    return True


def get_category(rel_path: str) -> str:
    """根据路径获取类别"""
    parts = rel_path.split(os.sep)
    for i, part in enumerate(parts):
        if part in CATEGORY_MAP:
            # 检查是否有子类别
            if i + 1 < len(parts) and parts[i + 1] in CATEGORY_MAP:
                return CATEGORY_MAP[parts[i + 1]]
            return CATEGORY_MAP[part]
    return "其他"


def process_document(file_path: Path, dry_run: bool = False) -> Optional[DocumentSummary]:
    """处理单个文档"""
    rel_path = str(file_path.relative_to(DOCS_DIR))
    
    if not should_process_file(rel_path):
        return None
    
    try:
        content = file_path.read_text(encoding='utf-8')
    except Exception as e:
        print(f"  错误: 无法读取 {rel_path}: {e}")
        return None
    
    # 检查是否已有摘要 - 如果已有，需要更新
    has_existing_summary = '📌 **内容摘要**' in content or '📌 内容摘要' in content
    
    if has_existing_summary:
        # 移除旧的摘要区块，以便重新生成
        # 找到摘要区块的起始和结束位置
        lines = content.split('\n')
        start_idx = -1
        end_idx = -1
        
        for i, line in enumerate(lines):
            if '📌 **内容摘要**' in line or '📌 内容摘要' in line:
                # 找到上一个 --- 或文档开头
                for j in range(i-1, -1, -1):
                    if lines[j].strip() == '---':
                        start_idx = j
                        break
                if start_idx == -1:
                    start_idx = max(0, i - 1)
            
            if start_idx != -1 and end_idx == -1:
                # 查找结束位置
                if i > start_idx + 1 and line.strip() == '---':
                    # 检查下一行是否为空或标题
                    if i + 1 < len(lines) and (lines[i+1].strip() == '' or lines[i+1].startswith('#')):
                        end_idx = i + 1
                        break
        
        if start_idx != -1 and end_idx != -1:
            # 移除旧摘要
            content = '\n'.join(lines[:start_idx] + lines[end_idx:])
        else:
            # 无法精确定位，跳过
            print(f"  警告: 无法更新 {rel_path} 的摘要")
            return None
    
    # 提取标题
    title = extract_title(content)
    
    # 获取类别
    category = get_category(rel_path)
    
    # 确定难度级别
    difficulty = get_difficulty_level(rel_path, title)
    
    # 估算阅读时间
    read_time = estimate_read_time(len(content), difficulty)
    
    # 生成关键词
    keywords = generate_keywords(title, category, content)
    
    # 生成学习目标
    learning_goals = generate_learning_goals(title, keywords, difficulty)
    
    # 生成摘要
    summary_text = generate_summary(title, category, keywords, difficulty)
    
    # 生成前置知识
    prerequisites = generate_prerequisites(rel_path, difficulty)
    
    # 创建摘要对象
    summary = DocumentSummary(
        path=rel_path,
        title=title,
        summary=summary_text,
        keywords=keywords,
        learning_goals=learning_goals,
        difficulty=difficulty,
        read_time=read_time,
        prerequisites=prerequisites,
        category=category,
    )
    
    if not dry_run:
        # 创建摘要区块
        summary_block = create_summary_block(summary)
        
        # 找到标题后的插入位置
        lines = content.split('\n')
        insert_pos = 0
        for i, line in enumerate(lines):
            if line.startswith('# ') and not line.startswith('##'):
                insert_pos = i + 1
                break
        
        # 插入摘要
        new_lines = lines[:insert_pos] + [''] + summary_block.split('\n') + lines[insert_pos:]
        new_content = '\n'.join(new_lines)
        
        # 写回文件
        file_path.write_text(new_content, encoding='utf-8')
    
    return summary


def generate_index(summaries: List[DocumentSummary], dry_run: bool = False):
    """生成摘要索引文档"""
    index_path = DOCS_DIR / "08_附录/03_索引/03.4_文档摘要索引.md"
    
    lines = [
        "# 03.4 文档摘要索引",
        "",
        "> **本索引包含所有主要文档的内容摘要、关键词和学习目标**",
        "",
        f"**生成时间**: {datetime.now().strftime('%Y-%m-%d %H:%M')}",
        f"**文档总数**: {len(summaries)}",
        "",
        "---",
        "",
        "## 📑 快速导航",
        "",
    ]
    
    # 按类别分组
    by_category = {}
    for s in summaries:
        cat = s.category
        if cat not in by_category:
            by_category[cat] = []
        by_category[cat].append(s)
    
    # 添加类别导航
    for cat in sorted(by_category.keys()):
        anchor = cat.replace(" ", "-").replace("&", "")
        lines.append(f"- [{cat}](#{anchor}) ({len(by_category[cat])}篇)")
    
    lines.extend([
        "",
        "---",
        "",
    ])
    
    # 为每个类别生成内容
    for cat in sorted(by_category.keys()):
        anchor = cat.replace(" ", "-").replace("&", "")
        lines.extend([
            f"## {cat}",
            "",
        ])
        
        for s in sorted(by_category[cat], key=lambda x: x.path):
            lines.extend([
                f"### [{s.title}](../{s.path})",
                "",
                f"**路径**: `{s.path}`",
                "",
                f"**摘要**: {s.summary}",
                "",
                f"**关键词**: {', '.join(s.keywords)}",
                "",
                f"🎯 **难度**: {s.difficulty} | ⏱️ **时间**: {s.read_time}",
                "",
                "**学习目标**:",
            ])
            for goal in s.learning_goals:
                lines.append(f"- {goal}")
            lines.append("")
    
    content = '\n'.join(lines)
    
    if not dry_run:
        # 确保目录存在
        index_path.parent.mkdir(parents=True, exist_ok=True)
        index_path.write_text(content, encoding='utf-8')
        print(f"\n索引已生成: {index_path}")
    
    return content


def main():
    """主函数"""
    dry_run = '--dry-run' in sys.argv
    index_only = '--index-only' in sys.argv
    
    print("=" * 60)
    print("FormalScience 文档摘要生成器")
    print("=" * 60)
    print(f"工作目录: {DOCS_DIR}")
    print(f"模式: {'干运行(不修改文件)' if dry_run else '实际执行'}")
    print()
    
    # 收集所有需要处理的文档
    all_md_files = list(DOCS_DIR.rglob("*.md"))
    print(f"总共发现 {len(all_md_files)} 个 Markdown 文件")
    
    # 处理文档
    summaries = []
    processed = 0
    skipped = 0
    errors = 0
    
    for file_path in all_md_files:
        rel_path = str(file_path.relative_to(DOCS_DIR))
        
        if not should_process_file(rel_path):
            skipped += 1
            continue
        
        try:
            summary = process_document(file_path, dry_run=dry_run or index_only)
            if summary:
                summaries.append(summary)
                processed += 1
                if processed % 10 == 0:
                    print(f"  已处理: {processed} 个文档...")
            else:
                skipped += 1
        except Exception as e:
            print(f"  错误处理 {rel_path}: {e}")
            errors += 1
    
    print()
    print(f"处理完成:")
    print(f"  - 成功处理: {processed} 个文档")
    print(f"  - 跳过: {skipped} 个文件")
    print(f"  - 错误: {errors} 个")
    print()
    
    # 生成索引
    if summaries:
        print("正在生成摘要索引...")
        generate_index(summaries, dry_run=dry_run)
        print()
    
    print("=" * 60)
    print("任务完成!")
    print("=" * 60)


if __name__ == "__main__":
    main()
