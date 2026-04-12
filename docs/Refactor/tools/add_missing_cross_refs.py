#!/usr/bin/env python3
"""为新增模块添加标准化交叉引用链接"""

from pathlib import Path

DOCS_ROOT = Path("docs/Refactor")

# 新增模块的交叉引用定义
NEW_MODULE_REFS = {
    '09_统计学': [
        ('01_数学基础/05_概率论与测度论/05.1_测度论基础.md', '测度论'),
        ('01_数学基础/05_概率论与测度论/05.2_概率论基础.md', '概率论'),
        ('10_信息论/01_香农信息论基础/01.2_熵的定义与性质.md', '信息论'),
        ('12_决策与博弈论/01_决策理论基础/01.2_期望效用理论.md', '决策理论'),
    ],
    '10_信息论': [
        ('01_数学基础/05_概率论与测度论/05.2_概率论基础.md', '概率论'),
        ('09_统计学/02_概率论基础/02.3_概率分布.md', '概率分布'),
        ('11_系统科学/03_复杂系统/03.1_复杂性度量.md', '复杂性度量'),
    ],
    '11_系统科学': [
        ('01_数学基础/04_分析学/04.1_实分析.md', '实分析'),
        ('09_统计学/05_数理统计/05.1_统计决策理论.md', '统计决策'),
        ('10_信息论/01_香农信息论基础/01.2_熵的定义与性质.md', '熵与信息'),
    ],
    '12_决策与博弈论': [
        ('01_数学基础/05_概率论与测度论/05.2_概率论基础.md', '概率论'),
        ('09_统计学/04_贝叶斯统计/04.1_贝叶斯定理.md', '贝叶斯统计'),
        ('02_形式语言/02_类型论/02.4_类型论与逻辑.md', '博弈逻辑'),
    ],
    '13_认知科学形式模型': [
        ('02_形式语言/02_类型论/02.1_简单类型论.md', '类型论'),
        ('09_统计学/04_贝叶斯统计/04.3_贝叶斯推断.md', '贝叶斯推断'),
        ('11_系统科学/02_控制论/02.1_反馈系统.md', '反馈系统'),
    ],
    '14_形式语言学': [
        ('02_形式语言/01_形式语言基础/01.1_形式语法.md', '形式语法'),
        ('02_形式语言/02_类型论/02.1_简单类型论.md', '类型论语义'),
        ('10_信息论/01_香农信息论基础/01.1_信息的度量.md', '语言信息量'),
    ],
    '15_社会科学形式化': [
        ('01_数学基础/02_代数学/02.1_抽象代数.md', '代数结构'),
        ('09_统计学/03_推断统计/03.1_点估计.md', '统计推断'),
        ('12_决策与博弈论/02_博弈论基础/02.2_纳什均衡.md', '博弈论'),
    ],
}


def add_cross_refs_to_index(module_name, refs):
    """为模块索引添加交叉引用链接"""
    index_path = DOCS_ROOT / module_name / '_index.md'
    if not index_path.exists():
        print(f"  跳过: {index_path} 不存在")
        return 0
    
    with open(index_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # 如果已有标准格式的相关模块链接，跳过
    if '## 🔗 相关模块链接' in content:
        print(f"  已存在: {module_name}")
        return 0
    
    # 在文件末尾添加
    section = "\n\n## 🔗 相关模块链接\n\n"
    for ref_path, desc in refs:
        ref_file = DOCS_ROOT / ref_path
        if ref_file.exists():
            # 计算相对路径
            rel_path = ref_path
            section += f"- [{desc}](../{rel_path})\n"
    
    content = content.rstrip() + section
    
    with open(index_path, 'w', encoding='utf-8') as f:
        f.write(content)
    
    print(f"  更新: {module_name}")
    return len(refs)


def main():
    print("=" * 60)
    print("添加新增模块交叉引用")
    print("=" * 60)
    
    total_refs = 0
    for module, refs in NEW_MODULE_REFS.items():
        count = add_cross_refs_to_index(module, refs)
        total_refs += count
    
    print(f"\n总共添加 {total_refs} 个引用链接")
    print("=" * 60)


if __name__ == '__main__':
    main()
