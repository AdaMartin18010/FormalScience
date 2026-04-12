#!/usr/bin/env python3
"""
FormalScience Concept目录占位符修复工具
扫描并修复Markdown文件中的占位符（"- |- |- |- "或类似模式）
"""

import os
import re
import shutil
from pathlib import Path
from datetime import datetime
from collections import defaultdict

# 配置
CONCEPT_DIR = Path("e:/_src/FormalScience/Concept")
BACKUP_DIR = CONCEPT_DIR / "backups_placeholder_fix"
REPORT_FILE = CONCEPT_DIR / "PLACEHOLDER_FIX_REPORT.md"

# 占位符模式
PLACEHOLDER_PATTERNS = [
    r'\| - \| - \| - \|',  # | - | - | - |
    r'\| - \| - \|',       # | - | - |
    r'\|-\|-\|-\|',        # |-|-|-|
    r'\| - \| - \| - \| - \|',  # | - | - | - | - |
]

# 占位符分类规则
PLACEHOLDER_CATEGORIES = {
    'comparison_matrix': ['对比', '比较', 'Comparison', 'Matrix', '矩阵'],
    'decision_tree': ['决策', 'Decision', 'Tree', '路径', 'Pathway'],
    'performance_data': ['性能', 'Performance', '成本', 'Cost', '效率', '吞吐量', '延迟'],
    'theory_content': ['理论', 'Theory', '定理', 'Theorem', '形式化', 'Formal'],
    'table_summary': ['总计', 'Total', '汇总', 'Summary', '收入'],
}

def find_markdown_files():
    """递归查找所有Markdown文件"""
    md_files = []
    for root, dirs, files in os.walk(CONCEPT_DIR):
        # 跳过备份目录
        if 'backups_placeholder_fix' in root:
            continue
        for file in files:
            if file.endswith('.md'):
                md_files.append(Path(root) / file)
    return md_files

def scan_placeholders(file_path):
    """扫描文件中的占位符"""
    placeholders = []
    try:
        with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
            lines = f.readlines()
            for i, line in enumerate(lines, 1):
                for pattern in PLACEHOLDER_PATTERNS:
                    if re.search(pattern, line):
                        placeholders.append({
                            'line_num': i,
                            'line_content': line.rstrip(),
                            'pattern': pattern
                        })
    except Exception as e:
        print(f"Error reading {file_path}: {e}")
    return placeholders

def categorize_placeholder(line_content, file_path):
    """根据内容和文件路径分类占位符"""
    content_lower = line_content.lower()
    file_lower = str(file_path).lower()
    
    # 检查文件路径关键词
    for category, keywords in PLACEHOLDER_CATEGORIES.items():
        for keyword in keywords:
            if keyword.lower() in file_lower or keyword.lower() in content_lower:
                return category
    
    # 默认分类
    return 'general_table'

def generate_fix_content(category, line_content, context):
    """根据分类生成修复内容"""
    fixes = {
        'comparison_matrix': {
            '| - | - | - |': '| 待补充 | 待补充 | 待补充 |',
            '| - | - |': '| 待补充 | 待补充 |',
        },
        'decision_tree': {
            '| - | - | - |': '| 评估中 | 评估中 | 评估中 |',
            '| - | - |': '| 评估中 | 评估中 |',
        },
        'performance_data': {
            '| - | - | - |': '| N/A | N/A | N/A |',
            '| - | - |': '| N/A | N/A |',
        },
        'theory_content': {
            '| - | - | - |': '| [待理论验证] | [待理论验证] | [待理论验证] |',
            '| - | - |': '| [待理论验证] | [待理论验证] |',
        },
        'table_summary': {
            '| - | - | - |': '| - | - | - |',  # 汇总行保持原样
            '| - | - |': '| - | - |',
        },
        'general_table': {
            '| - | - | - |': '| 待补充 | 待补充 | 待补充 |',
            '| - | - |': '| 待补充 | 待补充 |',
        }
    }
    
    # 返回对应分类的修复，如果没有则使用通用修复
    category_fixes = fixes.get(category, fixes['general_table'])
    for old, new in category_fixes.items():
        if old in line_content:
            return line_content.replace(old, new)
    
    return line_content

def create_backup(file_path):
    """创建文件备份"""
    rel_path = file_path.relative_to(CONCEPT_DIR)
    backup_path = BACKUP_DIR / rel_path
    backup_path.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(file_path, backup_path)
    return backup_path

def fix_file(file_path, placeholders):
    """修复文件中的占位符"""
    try:
        with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()
        
        original_content = content
        fixes_made = []
        
        for ph in placeholders:
            line_num = ph['line_num']
            line_content = ph['line_content']
            category = categorize_placeholder(line_content, file_path)
            
            # 获取文件所有行
            lines = content.split('\n')
            if line_num <= len(lines):
                old_line = lines[line_num - 1]
                new_line = generate_fix_content(category, old_line, None)
                
                if old_line != new_line:
                    lines[line_num - 1] = new_line
                    fixes_made.append({
                        'line_num': line_num,
                        'old': old_line,
                        'new': new_line,
                        'category': category
                    })
        
        if fixes_made:
            content = '\n'.join(lines)
            with open(file_path, 'w', encoding='utf-8') as f:
                f.write(content)
        
        return fixes_made
    except Exception as e:
        print(f"Error fixing {file_path}: {e}")
        return []

def generate_report(results, total_files, total_placeholders):
    """生成修复报告"""
    report = f"""# Concept目录占位符修复报告

## 修复概览

- **扫描时间**: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}
- **扫描文件数**: {total_files}
- **发现占位符**: {total_placeholders}
- **修复文件数**: {len([r for r in results if r['fixes']])}
- **总修复数**: {sum(len(r['fixes']) for r in results)}

## 按分类统计

"""
    
    # 统计分类
    category_stats = defaultdict(int)
    for r in results:
        for fix in r['fixes']:
            category_stats[fix['category']] += 1
    
    for category, count in sorted(category_stats.items(), key=lambda x: -x[1]):
        report += f"- **{category}**: {count} 处\n"
    
    report += "\n## 详细修复记录\n\n"
    
    for r in sorted(results, key=lambda x: -len(x['fixes'])):
        if r['fixes']:
            rel_path = r['file'].relative_to(CONCEPT_DIR)
            report += f"### {rel_path}\n\n"
            report += f"**修复数**: {len(r['fixes'])}\n\n"
            report += "| 行号 | 分类 | 原内容 | 修复后 |\n"
            report += "|------|------|--------|--------|\n"
            
            for fix in r['fixes']:
                old_short = fix['old'][:50] + '...' if len(fix['old']) > 50 else fix['old']
                new_short = fix['new'][:50] + '...' if len(fix['new']) > 50 else fix['new']
                report += f"| {fix['line_num']} | {fix['category']} | `{old_short}` | `{new_short}` |\n"
            
            report += "\n"
    
    # 未修复的文件
    report += "## 仅发现占位符但未修复的文件\n\n"
    for r in results:
        if r['placeholders'] and not r['fixes']:
            rel_path = r['file'].relative_to(CONCEPT_DIR)
            report += f"- {rel_path}: {len(r['placeholders'])} 处\n"
    
    report += """
## 修复规则说明

### 分类定义
- **comparison_matrix**: 对比矩阵/表格中的占位符
- **decision_tree**: 决策树/路径分析中的占位符
- **performance_data**: 性能数据/成本数据中的占位符
- **theory_content**: 理论内容/定理证明中的占位符
- **table_summary**: 表格汇总行中的占位符（保持原样）
- **general_table**: 通用表格中的占位符

### 修复标记
- `待补充`: 需要人工补充内容
- `评估中`: 决策路径待评估
- `N/A`: 不适用或数据不可用
- `[待理论验证]`: 需要理论验证的内容

## 备份信息

所有修复的文件都已备份到: `{backup_dir}`

## 后续建议

1. 检查所有标记为"待补充"的内容
2. 验证决策树中的"评估中"标记
3. 补充性能数据中的具体数值
4. 完善理论验证内容

---
**报告生成**: {timestamp}
""".format(backup_dir=BACKUP_DIR, timestamp=datetime.now().strftime('%Y-%m-%d %H:%M:%S'))
    
    with open(REPORT_FILE, 'w', encoding='utf-8') as f:
        f.write(report)
    
    return report

def main():
    print("="*60)
    print("FormalScience Concept目录占位符修复工具")
    print("="*60)
    
    # 1. 查找所有Markdown文件
    print("\n[1/5] 扫描Markdown文件...")
    md_files = find_markdown_files()
    print(f"找到 {len(md_files)} 个Markdown文件")
    
    # 2. 扫描占位符
    print("\n[2/5] 扫描占位符...")
    results = []
    total_placeholders = 0
    
    for i, file_path in enumerate(md_files, 1):
        placeholders = scan_placeholders(file_path)
        if placeholders:
            total_placeholders += len(placeholders)
            results.append({
                'file': file_path,
                'placeholders': placeholders,
                'fixes': []
            })
            print(f"  [{i}/{len(md_files)}] {file_path.name}: {len(placeholders)} 处占位符")
    
    print(f"\n共发现 {total_placeholders} 处占位符，涉及 {len(results)} 个文件")
    
    # 3. 创建备份
    print("\n[3/5] 创建文件备份...")
    for r in results:
        backup_path = create_backup(r['file'])
        print(f"  备份: {backup_path}")
    
    # 4. 修复占位符
    print("\n[4/5] 修复占位符...")
    total_fixes = 0
    for r in results:
        fixes = fix_file(r['file'], r['placeholders'])
        r['fixes'] = fixes
        total_fixes += len(fixes)
        if fixes:
            print(f"  ✓ {r['file'].name}: 修复 {len(fixes)} 处")
    
    # 5. 生成报告
    print("\n[5/5] 生成修复报告...")
    report = generate_report(results, len(md_files), total_placeholders)
    
    print("\n" + "="*60)
    print("修复完成!")
    print("="*60)
    print(f"扫描文件: {len(md_files)}")
    print(f"发现占位符: {total_placeholders} 处")
    print(f"修复文件: {len([r for r in results if r['fixes']])} 个")
    print(f"总修复数: {total_fixes} 处")
    print(f"报告位置: {REPORT_FILE}")
    print(f"备份位置: {BACKUP_DIR}")
    print("="*60)

if __name__ == "__main__":
    main()
