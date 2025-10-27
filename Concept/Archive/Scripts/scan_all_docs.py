#!/usr/bin/env python3
"""
系统扫描所有Information_Theory_Perspective文档
识别需要扩充的文档清单
"""

import os
import re
from pathlib import Path
from collections import defaultdict

def count_lines(filepath):
    """统计文件行数"""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            return len(f.readlines())
    except:
        return 0

def analyze_document(filepath):
    """分析单个文档"""
    lines = count_lines(filepath)
    
    # 分类
    if lines < 200:
        category = "极短"
    elif lines < 400:
        category = "短"
    elif lines < 700:
        category = "中等"
    else:
        category = "完整"
    
    return {
        'path': filepath,
        'lines': lines,
        'category': category,
        'priority': 1 if lines < 200 else (2 if lines < 400 else (3 if lines < 700 else 4))
    }

def main():
    base_dir = Path('Information_Theory_Perspective')
    
    if not base_dir.exists():
        print(f"错误: 目录 {base_dir} 不存在")
        return
    
    # 扫描所有markdown文件
    all_docs = []
    for md_file in base_dir.rglob('*.md'):
        if md_file.name != 'README.md':  # 排除README
            doc_info = analyze_document(md_file)
            all_docs.append(doc_info)
    
    # 按行数排序
    all_docs.sort(key=lambda x: x['lines'])
    
    # 统计
    category_stats = defaultdict(list)
    for doc in all_docs:
        category_stats[doc['category']].append(doc)
    
    # 生成报告
    print("="*80)
    print("Information_Theory_Perspective 文档扫描报告")
    print("="*80)
    print(f"\n总文档数: {len(all_docs)}\n")
    
    print("分类统计:")
    print("-"*80)
    for category in ["极短", "短", "中等", "完整"]:
        docs = category_stats[category]
        print(f"{category} (<200行 / 200-400行 / 400-700行 / >700行): {len(docs)}个")
    
    print("\n" + "="*80)
    print("需要扩充的文档清单（优先级排序）")
    print("="*80)
    
    # P1: 极短文档
    print("\n【P1优先级：极短文档 <200行】")
    print("-"*80)
    for i, doc in enumerate(category_stats["极短"], 1):
        rel_path = doc['path'].relative_to(base_dir)
        print(f"{i}. {rel_path} ({doc['lines']}行)")
    
    # P2: 短文档
    print("\n【P2优先级：短文档 200-400行】")
    print("-"*80)
    for i, doc in enumerate(category_stats["短"], 1):
        rel_path = doc['path'].relative_to(base_dir)
        print(f"{i}. {rel_path} ({doc['lines']}行)")
    
    # P3: 中等文档
    print("\n【P3优先级：中等文档 400-700行】")
    print("-"*80)
    for i, doc in enumerate(category_stats["中等"], 1):
        rel_path = doc['path'].relative_to(base_dir)
        print(f"{i}. {rel_path} ({doc['lines']}行)")
    
    # 完整文档
    print("\n【已完整：>700行，暂无需扩充】")
    print("-"*80)
    for i, doc in enumerate(category_stats["完整"], 1):
        rel_path = doc['path'].relative_to(base_dir)
        print(f"{i}. {rel_path} ({doc['lines']}行)")
    
    # 生成Markdown报告
    report_path = Path('Concept/SCAN_RESULT_REPORT.md')
    with open(report_path, 'w', encoding='utf-8') as f:
        f.write("# Information_Theory_Perspective 文档扫描报告\n\n")
        f.write(f"**扫描时间**: 2025-10-27\n")
        f.write(f"**总文档数**: {len(all_docs)}\n\n")
        f.write("---\n\n")
        
        f.write("## 📊 分类统计\n\n")
        f.write("| 类别 | 数量 | 行数范围 | 状态 |\n")
        f.write("|------|------|---------|------|\n")
        f.write(f"| 极短 | {len(category_stats['极短'])} | <200行 | 🔴 急需扩充 |\n")
        f.write(f"| 短 | {len(category_stats['短'])} | 200-400行 | 🟡 需要扩充 |\n")
        f.write(f"| 中等 | {len(category_stats['中等'])} | 400-700行 | 🟢 可扩充 |\n")
        f.write(f"| 完整 | {len(category_stats['完整'])} | >700行 | ✅ 暂无需扩充 |\n\n")
        
        f.write("---\n\n")
        
        # P1
        f.write("## 🔴 P1优先级：极短文档 (<200行)\n\n")
        f.write(f"**数量**: {len(category_stats['极短'])}个\n\n")
        for i, doc in enumerate(category_stats["极短"], 1):
            rel_path = doc['path'].relative_to(base_dir)
            f.write(f"{i}. `{rel_path}` - **{doc['lines']}行**\n")
        f.write("\n")
        
        # P2
        f.write("## 🟡 P2优先级：短文档 (200-400行)\n\n")
        f.write(f"**数量**: {len(category_stats['短'])}个\n\n")
        for i, doc in enumerate(category_stats["短"], 1):
            rel_path = doc['path'].relative_to(base_dir)
            f.write(f"{i}. `{rel_path}` - **{doc['lines']}行**\n")
        f.write("\n")
        
        # P3
        f.write("## 🟢 P3优先级：中等文档 (400-700行)\n\n")
        f.write(f"**数量**: {len(category_stats['中等'])}个\n\n")
        for i, doc in enumerate(category_stats["中等"], 1):
            rel_path = doc['path'].relative_to(base_dir)
            f.write(f"{i}. `{rel_path}` - **{doc['lines']}行**\n")
        f.write("\n")
        
        # 完整
        f.write("## ✅ 已完整文档 (>700行)\n\n")
        f.write(f"**数量**: {len(category_stats['完整'])}个\n\n")
        for i, doc in enumerate(category_stats["完整"], 1):
            rel_path = doc['path'].relative_to(base_dir)
            f.write(f"{i}. `{rel_path}` - **{doc['lines']}行**\n")
        f.write("\n")
        
        f.write("---\n\n")
        f.write("## 📋 下一步行动\n\n")
        f.write("### Batch 2计划\n\n")
        f.write(f"**目标**: 扩充{len(category_stats['极短'])}个P1文档\n")
        f.write("**策略**: 按目录批量处理\n")
        f.write("**预计时间**: ~{0}小时\n\n".format(len(category_stats['极短']) * 1))
        
        f.write("### Batch 3-5计划\n\n")
        f.write(f"**目标**: 扩充{len(category_stats['短'])}个P2文档\n")
        f.write("**预计时间**: ~{0}小时\n\n".format(len(category_stats['短']) * 0.75))
        
        f.write("### 长期计划\n\n")
        f.write(f"**目标**: 优化{len(category_stats['中等'])}个P3文档\n")
        f.write("**预计时间**: ~{0}小时\n\n".format(len(category_stats['中等']) * 0.5))
    
    print(f"\n\n✅ 报告已生成: {report_path}")
    print("="*80)

if __name__ == "__main__":
    main()

