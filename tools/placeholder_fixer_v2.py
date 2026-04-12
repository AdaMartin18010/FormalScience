#!/usr/bin/env python3
"""
FormalScience Concept目录占位符修复工具 V2
扫描并修复Markdown文件中的各种占位符模式
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
REPORT_FILE = CONCEPT_DIR / "PLACEHOLDER_FIX_REPORT_V2.md"

# 扩展占位符模式 - 包含更多类型
PLACEHOLDER_PATTERNS = [
    # 四连横线 | - | - | - | - |
    (r'\|\s*-\s*\|\s*-\s*\|\s*-\s*\|\s*-\s*\|', 'quad_dash', '| 待补充 | 待补充 | 待补充 | 待补充 |'),
    # 三连横线 | - | - | - |
    (r'\|\s*-\s*\|\s*-\s*\|\s*-\s*\|', 'triple_dash', '| 待补充 | 待补充 | 待补充 |'),
    # 双连横线 | - | - |
    (r'\|\s*-\s*\|\s*-\s*\|', 'double_dash', '| 待补充 | 待补充 |'),
    # N/A 占位符
    (r'\|\s*N/A\s*\|', 'na_marker', '| 数据待补充 |'),
    (r'\|\s*n/a\s*\|', 'na_marker', '| 数据待补充 |'),
    # 待补充/待完善标记
    (r'\|\s*待补充\s*\|', 'pending_content', '| [需人工完善] |'),
    (r'\|\s*待完善\s*\|', 'pending_content', '| [需人工完善] |'),
    # TBD/TODO标记
    (r'\|\s*TBD\s*\|', 'tbd_marker', '| [待确定] |'),
    (r'\|\s*TODO\s*\|', 'todo_marker', '| [待完成] |'),
]

# 占位符分类规则
PLACEHOLDER_CATEGORIES = {
    'comparison_matrix': ['对比', '比较', 'Comparison', 'Matrix', '矩阵', '对标'],
    'decision_tree': ['决策', 'Decision', 'Tree', '路径', 'Pathway'],
    'performance_data': ['性能', 'Performance', '成本', 'Cost', '效率', '吞吐量', '延迟', 'latency', 'throughput'],
    'theory_content': ['理论', 'Theory', '定理', 'Theorem', '形式化', 'Formal', '证明'],
    'table_summary': ['总计', 'Total', '汇总', 'Summary', '收入', '合计'],
}

def find_markdown_files():
    """递归查找所有Markdown文件"""
    md_files = []
    for root, dirs, files in os.walk(CONCEPT_DIR):
        if 'backups_placeholder_fix' in root:
            continue
        for file in files:
            if file.endswith('.md'):
                md_files.append(Path(root) / file)
    return md_files

def scan_placeholders(file_path):
    """扫描文件中的各种占位符"""
    placeholders = []
    try:
        with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
            lines = f.readlines()
            for i, line in enumerate(lines, 1):
                for pattern, ptype, replacement in PLACEHOLDER_PATTERNS:
                    if re.search(pattern, line):
                        placeholders.append({
                            'line_num': i,
                            'line_content': line.rstrip(),
                            'pattern': pattern,
                            'type': ptype,
                            'replacement': replacement
                        })
    except Exception as e:
        print(f"Error reading {file_path}: {e}")
    return placeholders

def categorize_placeholder(line_content, file_path):
    """根据内容和文件路径分类占位符"""
    content_lower = line_content.lower()
    file_lower = str(file_path).lower()
    
    for category, keywords in PLACEHOLDER_CATEGORIES.items():
        for keyword in keywords:
            if keyword.lower() in file_lower or keyword.lower() in content_lower:
                return category
    
    return 'general_table'

def get_contextual_replacement(category, original_replacement):
    """根据分类获取上下文化的替换内容"""
    contextual_fixes = {
        'comparison_matrix': {
            '| 待补充 | 待补充 | 待补充 | 待补充 |': '| 对比待补充 | 对比待补充 | 对比待补充 | 对比待补充 |',
            '| 待补充 | 待补充 | 待补充 |': '| 对比待补充 | 对比待补充 | 对比待补充 |',
            '| 待补充 | 待补充 |': '| 对比待补充 | 对比待补充 |',
        },
        'performance_data': {
            '| 待补充 | 待补充 | 待补充 | 待补充 |': '| N/A | N/A | N/A | N/A |',
            '| 待补充 | 待补充 | 待补充 |': '| N/A | N/A | N/A |',
            '| 待补充 | 待补充 |': '| N/A | N/A |',
        },
        'theory_content': {
            '| 待补充 | 待补充 | 待补充 | 待补充 |': '| [理论待验证] | [理论待验证] | [理论待验证] | [理论待验证] |',
            '| 待补充 | 待补充 | 待补充 |': '| [理论待验证] | [理论待验证] | [理论待验证] |',
            '| 待补充 | 待补充 |': '| [理论待验证] | [理论待验证] |',
        },
        'decision_tree': {
            '| 待补充 | 待补充 | 待补充 | 待补充 |': '| 评估中 | 评估中 | 评估中 | 评估中 |',
            '| 待补充 | 待补充 | 待补充 |': '| 评估中 | 评估中 | 评估中 |',
            '| 待补充 | 待补充 |': '| 评估中 | 评估中 |',
        },
        'table_summary': {
            '| 待补充 | 待补充 | 待补充 | 待补充 |': '| - | - | - | - |',
            '| 待补充 | 待补充 | 待补充 |': '| - | - | - |',
            '| 待补充 | 待补充 |': '| - | - |',
        },
    }
    
    category_fixes = contextual_fixes.get(category, {})
    return category_fixes.get(original_replacement, original_replacement)

def create_backup(file_path):
    """创建文件备份"""
    rel_path = file_path.relative_to(CONCEPT_DIR)
    backup_path = BACKUP_DIR / rel_path
    backup_path.parent.mkdir(parents=True, exist_ok=True)
    
    # 如果备份已存在，不覆盖
    if backup_path.exists():
        return backup_path
    
    shutil.copy2(file_path, backup_path)
    return backup_path

def fix_file(file_path, placeholders):
    """修复文件中的占位符"""
    try:
        with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()
        
        fixes_made = []
        lines = content.split('\n')
        
        for ph in placeholders:
            line_num = ph['line_num']
            pattern = ph['pattern']
            replacement = ph['replacement']
            category = categorize_placeholder(ph['line_content'], file_path)
            
            # 获取上下文化的替换
            actual_replacement = get_contextual_replacement(category, replacement)
            
            if line_num <= len(lines):
                old_line = lines[line_num - 1]
                # 使用正则替换
                new_line = re.sub(pattern, actual_replacement, old_line)
                
                if old_line != new_line:
                    lines[line_num - 1] = new_line
                    fixes_made.append({
                        'line_num': line_num,
                        'old': old_line,
                        'new': new_line,
                        'category': category,
                        'type': ph['type']
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
    report = f"""# Concept目录占位符修复报告 V2

## 修复概览

- **扫描时间**: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}
- **扫描文件数**: {total_files}
- **发现占位符**: {total_placeholders}
- **修复文件数**: {len([r for r in results if r['fixes']])}
- **总修复数**: {sum(len(r['fixes']) for r in results)}

## 按类型统计

"""
    
    # 统计类型
    type_stats = defaultdict(int)
    for r in results:
        for fix in r['fixes']:
            type_stats[fix['type']] += 1
    
    for ptype, count in sorted(type_stats.items(), key=lambda x: -x[1]):
        report += f"- **{ptype}**: {count} 处\n"
    
    report += "\n## 按分类统计\n\n"
    
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
            report += "| 行号 | 类型 | 分类 | 原内容 | 修复后 |\n"
            report += "|------|------|------|--------|--------|\n"
            
            for fix in r['fixes']:
                old_short = fix['old'][:40] + '...' if len(fix['old']) > 40 else fix['old']
                new_short = fix['new'][:40] + '...' if len(fix['new']) > 40 else fix['new']
                report += f"| {fix['line_num']} | {fix['type']} | {fix['category']} | `{old_short}` | `{new_short}` |\n"
            
            report += "\n"
    
    report += f"""
## 修复规则说明

### 占位符类型
- **quad_dash**: 四连横线 | - | - | - | - |
- **triple_dash**: 三连横线 | - | - | - |
- **double_dash**: 双连横线 | - | - |
- **na_marker**: N/A 标记
- **pending_content**: 待补充/待完善标记
- **tbd_marker**: TBD标记
- **todo_marker**: TODO标记

### 分类替换规则
- **comparison_matrix**: 使用"对比待补充"
- **performance_data**: 使用"N/A"
- **theory_content**: 使用"[理论待验证]"
- **decision_tree**: 使用"评估中"
- **table_summary**: 保留"-"作为汇总标记
- **general_table**: 使用"待补充"

## 备份信息

所有修复的文件都已备份到: `{BACKUP_DIR}`

## 后续建议

1. 检查所有标记为"待补充"的内容
2. 验证决策树中的"评估中"标记
3. 补充性能数据中的具体数值
4. 完善理论验证内容

---
**报告生成**: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}
"""
    
    with open(REPORT_FILE, 'w', encoding='utf-8') as f:
        f.write(report)
    
    return report

def main():
    print("="*60)
    print("FormalScience Concept目录占位符修复工具 V2")
    print("="*60)
    
    # 1. 查找所有Markdown文件
    print("\n[1/5] 扫描Markdown文件...")
    md_files = find_markdown_files()
    print(f"找到 {len(md_files)} 个Markdown文件")
    
    # 2. 扫描占位符
    print("\n[2/5] 扫描各种类型占位符...")
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
            if len(placeholders) > 0:
                print(f"  [{i}/{len(md_files)}] {file_path.name}: {len(placeholders)} 处")
    
    print(f"\n共发现 {total_placeholders} 处占位符，涉及 {len(results)} 个文件")
    
    # 3. 创建备份
    print("\n[3/5] 创建文件备份...")
    backup_count = 0
    for r in results:
        backup_path = create_backup(r['file'])
        if backup_path:
            backup_count += 1
    print(f"  已备份 {backup_count} 个文件")
    
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
