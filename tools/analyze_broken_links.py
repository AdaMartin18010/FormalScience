#!/usr/bin/env python3
"""
分析无效链接的详细分类统计工具
"""

import json
from pathlib import Path
from collections import defaultdict

# 加载报告
report_path = Path("docs/Refactor/.reports/link_check_report.json")
with open(report_path, 'r', encoding='utf-8') as f:
    report = json.load(f)

broken_links = report['broken_internal_links']

# 分类统计
categories = {
    "模板占位符": [],  # path/to, doc-a, doc-b 等示例链接
    "锚点问题": [],    # 锚点不存在
    "父目录引用": [],  # ../ 开头的链接
    "缺失文件": [],    # 文件确实不存在
    "其他": []
}

for link in broken_links:
    target = link['target']
    reason = link['reason']
    source = link['source']
    
    # 判断类型
    if 'path/to' in target or 'doc-a' in target or 'doc-b' in target or 'file.md' in target:
        categories["模板占位符"].append(link)
    elif '锚点不存在' in reason:
        categories["锚点问题"].append(link)
    elif target.startswith('../'):
        categories["父目录引用"].append(link)
    elif '文件不存在' in reason:
        categories["缺失文件"].append(link)
    else:
        categories["其他"].append(link)

# 统计
total = len(broken_links)
print("=" * 60)
print("无效链接分类统计")
print("=" * 60)

for cat, links in categories.items():
    pct = len(links) / total * 100 if total > 0 else 0
    print(f"\n{cat}: {len(links)} ({pct:.1f}%)")
    
    # 显示前5个示例
    for link in links[:5]:
        print(f"  - {link['source']} -> {link['target']}")
    if len(links) > 5:
        print(f"  ... 还有 {len(links) - 5} 个")

# 统计涉及的问题文件
problem_files = defaultdict(int)
for link in broken_links:
    # 排除模板文件
    if '.templates' not in link['source']:
        problem_files[link['source']] += 1

print("\n" + "=" * 60)
print("问题最严重的文件（排除模板）")
print("=" * 60)
for file, count in sorted(problem_files.items(), key=lambda x: x[1], reverse=True)[:20]:
    print(f"  {file}: {count} 个无效链接")

# 保存详细分析
analysis = {
    "categories": {k: [{"source": l['source'], "target": l['target'], "line": l['line']} for l in v] 
                   for k, v in categories.items()},
    "problem_files": dict(sorted(problem_files.items(), key=lambda x: x[1], reverse=True)),
    "summary": {
        "total_broken": total,
        "template_placeholders": len(categories["模板占位符"]),
        "anchor_issues": len(categories["锚点问题"]),
        "parent_dir_refs": len(categories["父目录引用"]),
        "missing_files": len(categories["缺失文件"]),
        "other": len(categories["其他"])
    }
}

analysis_path = Path("docs/Refactor/.reports/broken_links_analysis.json")
with open(analysis_path, 'w', encoding='utf-8') as f:
    json.dump(analysis, f, ensure_ascii=False, indent=2)

print(f"\n详细分析已保存至: {analysis_path}")

# 生成修复建议
print("\n" + "=" * 60)
print("修复建议优先级")
print("=" * 60)

if categories["模板占位符"]:
    print(f"""
【低优先级】模板占位符链接 ({len(categories["模板占位符"])}个)
建议: 这些是模板文件中的示例链接，无需修复
""")

if categories["父目录引用"]:
    print(f"""
【高优先级】父目录引用 ({len(categories["父目录引用"])}个)
建议: 检查这些引用是否正确指向根目录文件
示例: ../LICENSE, ../README.md 等
""")

if categories["锚点问题"]:
    print(f"""
【中优先级】锚点问题 ({len(categories["锚点问题"])}个)
建议: 检查文档中是否存在对应标题
或更新为正确的锚点名称
""")

if categories["缺失文件"]:
    print(f"""
【高优先级】缺失文件 ({len(categories["缺失文件"])}个)
建议: 
1. 检查文件是否被重命名或移动
2. 更新链接路径
3. 或创建缺失的文档
""")

print(f"""
【统计摘要】
- 总无效链接: {total}
- 有效内部链接: {report['statistics']['total_internal_links'] - total}
- 内部链接有效率: {(report['statistics']['total_internal_links'] - total) / report['statistics']['total_internal_links'] * 100:.1f}%
""")
