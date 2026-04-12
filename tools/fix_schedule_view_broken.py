#!/usr/bin/env python3
"""
修复Composed/schedule_formal_view的具体断链
"""

import re
from pathlib import Path

# 具体修复规则
FIXES = {
    # 文件路径 -> [(旧链接, 新链接或None), ...]
    'Composed/schedule_formal_view/14_存储调度系统/14.1_内存调度.md': [
        ('../../docs/Refactor/FormalRE/操作系统/内存调度理论.md', None),
    ],
    'Composed/schedule_formal_view/27_机密计算调度/README.md': [
        ('../24_安全调度/', None),
    ],
    'Composed/schedule_formal_view/30_工作流调度/30.3_Petri网调度模型.md': [
        ('../../../formal_lang_view/10_Petri网理论/', None),
    ],
    'Composed/schedule_formal_view/README.md': [
        ('../Concept/TuningCompute/', 'https://github.com/formalscience/Concept/tree/main/TuningCompute'),
    ],
    'Composed/schedule_formal_view/内容填充实施方案.md': [
        ('../06_调度模型/06.2_OS内核调度.md', '../06_调度模型/06.2_OS内核调度.md'),  # 检查是否存在
    ],
    'Composed/schedule_formal_view/内容补充完善计划与方案.md': [
        ('../06_调度模型/06.2_OS内核调度.md', '../06_调度模型/06.2_OS内核调度.md'),
    ],
}

# 数学公式修复 - 这些不是真正的链接
MATH_FIXES = [
    # LaTeX公式中的括号被误识别
    (r'\[next_state\]\(entity\)', '`next_state(entity)`'),
    (r'\[k\]\(y\[k\] - H\\hat\{x\}\[k\|k-1\]\)', '$k$'),
    (r'\[k\]\(y\[k\] - Hx̂\[k\|k-1\]\)', '$k$'),
    (r'\[\\mathbf\{L\}\]\(\\mathbf\{v\}\)', '$\\mathbf{L}(\\mathbf{v})$'),
    (r'\[\\mathbf\{L\}\]\(\\Delta \\mathbf\{L\}\(m', '$\\mathbf{L}(\\Delta \\mathbf{L}(m)$'),
]


def fix_file(file_path, dry_run=True):
    """修复单个文件"""
    rel_path = str(file_path).replace('\\', '/')
    
    if rel_path not in FIXES and 'FormalModel' not in rel_path:
        return []
        
    try:
        content = file_path.read_text(encoding='utf-8')
        original = content
        changes = []
        
        # 应用具体修复
        if rel_path in FIXES:
            for old_url, new_url in FIXES[rel_path]:
                pattern = re.escape(old_url)
                if new_url:
                    if re.search(pattern, content):
                        content = re.sub(pattern, new_url, content)
                        changes.append(f'{old_url} -> {new_url}')
                else:
                    # 删除链接，保留文本
                    link_pattern = rf'\[([^\]]+)\]\({re.escape(old_url)}\)'
                    def replace_link(match):
                        return f'**{match.group(1)}**'
                    new_content = re.sub(link_pattern, replace_link, content)
                    if new_content != content:
                        changes.append(f'Removed link to {old_url}')
                        content = new_content
                        
        # 修复数学公式
        if 'FormalModel' in rel_path or 'schedule_model' in rel_path:
            for pattern, replacement in MATH_FIXES:
                if re.search(pattern, content):
                    content = re.sub(pattern, replacement, content)
                    changes.append(f'Fixed math: {pattern[:30]}...')
                    
        if changes and not dry_run:
            file_path.write_text(content, encoding='utf-8')
            
        return changes
        
    except Exception as e:
        print(f"Error: {file_path}: {e}")
        return []


def main():
    import sys
    base_path = Path(sys.argv[1] if len(sys.argv) > 1 else ".")
    dry_run = '--apply' not in sys.argv
    
    all_changes = {}
    
    for file_rel, fixes in FIXES.items():
        file_path = base_path / file_rel
        if file_path.exists():
            changes = fix_file(file_path, dry_run)
            if changes:
                all_changes[file_rel] = changes
                
    # 处理FormalModel目录
    formalmodel_dir = base_path / 'Composed/schedule_formal_view/FormalModel'
    if formalmodel_dir.exists():
        for f in formalmodel_dir.rglob('*.md'):
            changes = fix_file(f, dry_run)
            if changes:
                rel = str(f.relative_to(base_path)).replace('\\', '/')
                all_changes[rel] = changes
                
    # 处理view目录下的schedule_model.md
    view_model = base_path / 'Composed/schedule_formal_view/view/schedule_model.md'
    if view_model.exists():
        changes = fix_file(view_model, dry_run)
        if changes:
            all_changes['Composed/schedule_formal_view/view/schedule_model.md'] = changes
    
    print(f"模式: {'干运行' if dry_run else '实际修复'}")
    print(f"修复文件数: {len(all_changes)}")
    
    for file, changes in all_changes.items():
        print(f"\n{file}:")
        for c in changes:
            print(f"  - {c}")
            
    if not dry_run:
        print("\n修复已应用。")
    else:
        print("\n使用 --apply 执行实际修复。")
        
    return len(all_changes)


if __name__ == "__main__":
    main()
