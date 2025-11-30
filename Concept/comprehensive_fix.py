#!/usr/bin/env python3
"""
全面修复Concept目录下所有Markdown文件的格式和结构问题
"""

import os
import re
from pathlib import Path

# 英文到中文的标题映射（常见术语）
TITLE_TRANSLATIONS = {
    'Blockchain Formal Language Foundations': '区块链形式语言基础',
    'Software Architecture Formal Language Evolution': '软件架构形式语言演进',
    'Philosophy Formal Language Integration': '哲学形式语言整合',
    'Legal System Formalization': '法律系统形式化',
    'Artificial Consciousness Design': '人工意识设计',
    'Cognitive Science Formal Language Models': '认知科学形式语言模型',
    'Mathematics Formal Language Foundations': '数学形式语言基础',
    'AI Consciousness Formal Language Bridge': 'AI意识形式语言桥梁',
    'LLM Formal Language Perspective': 'LLM形式语言视角',
    'Chomsky AI Formal Language Argument': '乔姆斯基AI形式语言论证',
    'Physics Chemistry Biology Economics Formal Language Perspective': '物理化学生物经济学形式语言视角',
    'Mathematics Imagination Formal Language Perspective': '数学想象形式语言视角',
    'Algorithm Theory Formal Language Perspective': '算法理论形式语言视角',
    'Knowledge Structure Formal Language Perspective': '知识结构形式语言视角',
    'Blockchain AI Software Architecture Integration': '区块链AI软件架构整合',
}

def extract_file_number(filename):
    """从文件名提取编号"""
    match = re.match(r'(\d+\.\d+)_', filename)
    if match:
        return match.group(1)
    return None

def get_theme_from_path(filepath):
    """从文件路径推断主题"""
    parts = Path(filepath).parts
    if 'FormalLanguage_Perspective' in parts:
        return '形式语言视角'
    elif 'AI_model_Perspective' in parts:
        return 'AI模型视角'
    elif 'Software_Perspective' in parts:
        return '软件视角'
    elif 'Program_Algorithm_Perspective' in parts:
        return '程序算法视角'
    elif 'Information_Theory_Perspective' in parts:
        return '信息论视角'
    elif 'Wasm_Perspective' in parts:
        return 'Wasm视角'
    else:
        return '形式语言视角'

def extract_title_from_filename(filename):
    """从文件名提取标题并翻译"""
    match = re.match(r'\d+\.\d+_(.+)\.md', filename)
    if match:
        title = match.group(1).replace('_', ' ')
        # 去掉冒号后的内容
        title = re.sub(r':.*$', '', title)
        title = re.sub(r'：.*$', '', title)
        
        # 尝试翻译
        if title in TITLE_TRANSLATIONS:
            return TITLE_TRANSLATIONS[title]
        
        # 如果包含已知关键词，尝试翻译
        for en, zh in TITLE_TRANSLATIONS.items():
            if en in title:
                return title.replace(en, zh)
        
        return title
    return None

def fix_all_issues(content, filepath):
    """修复所有格式问题"""
    filename = Path(filepath).name
    file_number = extract_file_number(filename)
    
    if not file_number:
        return content
    
    # 1. 修复重复的元数据
    lines = content.split('\n')
    result_lines = []
    seen_subtopic = False
    seen_theme = False
    
    for i, line in enumerate(lines):
        if re.match(r'> \*\*子主题编号\*\*:', line):
            if not seen_subtopic:
                result_lines.append(line)
                seen_subtopic = True
        elif re.match(r'> \*\*主题\*\*:', line):
            if not seen_theme:
                result_lines.append(line)
                seen_theme = True
        else:
            result_lines.append(line)
    
    content = '\n'.join(result_lines)
    
    # 2. 修复标题格式
    title_text = extract_title_from_filename(filename)
    if title_text:
        clean_number = file_number.lstrip('0').lstrip('.')
        if not clean_number:
            clean_number = file_number
        new_title = f"# {clean_number} {title_text}"
        content = re.sub(r'^# .+$', new_title, content, count=1, flags=re.MULTILINE)
    
    # 3. 确保元数据格式正确
    theme = get_theme_from_path(filepath)
    new_metadata = f"> **子主题编号**: {file_number}\n> **主题**: {theme}"
    
    # 删除所有现有的子主题编号和主题行
    content = re.sub(r'> \*\*子主题编号\*\*:.*\n', '', content)
    content = re.sub(r'> \*\*主题\*\*:.*\n', '', content)
    
    # 在标题后插入元数据
    if not re.search(r'> \*\*子主题编号\*\*:', content):
        pattern = r'(^# .+$\n)(\n)?'
        replacement = rf'\1\n{new_metadata}\n'
        content = re.sub(pattern, replacement, content, count=1, flags=re.MULTILINE)
    
    # 4. 修复章节编号格式（去掉空格）
    content = re.sub(r'^## (\d+) \. ', r'## \1 ', content, flags=re.MULTILINE)
    content = re.sub(r'^### (\d+) \. ', r'### \1 ', content, flags=re.MULTILINE)
    
    # 5. 修复目录中的主标题链接
    title_text = extract_title_from_filename(filename)
    if title_text:
        clean_number = file_number.lstrip('0').lstrip('.')
        if not clean_number:
            clean_number = file_number
        expected_title = f"{clean_number} {title_text}"
        # 生成锚点
        anchor = re.sub(r'[^\w\-]', '', expected_title.lower().replace(' ', '-'))
        # 修复目录中的链接
        content = re.sub(
            r'- \[([^\]]+)\]\(#[^\)]+\)',
            lambda m: f"- [{expected_title}](#{anchor})" if '目录' not in m.group(1) and 'Related' not in m.group(1) else m.group(0),
            content,
            count=1
        )
    
    return content

def process_file(filepath):
    """处理单个文件"""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
        
        original_content = content
        content = fix_all_issues(content, filepath)
        
        if content != original_content:
            with open(filepath, 'w', encoding='utf-8') as f:
                f.write(content)
            return True
        return False
    except Exception as e:
        print(f"✗ 错误: {filepath}: {e}")
        return False

def main():
    """主函数"""
    base_dir = Path(__file__).parent
    pattern = re.compile(r'^\d+\.\d+_.+\.md$')
    files_to_fix = []
    
    for root, dirs, files in os.walk(base_dir):
        if 'node_modules' in root or '.git' in root:
            continue
        for file in files:
            if pattern.match(file):
                files_to_fix.append(Path(root) / file)
    
    print(f"找到 {len(files_to_fix)} 个文件...\n")
    
    fixed = 0
    for filepath in sorted(files_to_fix):
        if process_file(filepath):
            print(f"✓ {filepath.name}")
            fixed += 1
    
    print(f"\n完成！修复了 {fixed}/{len(files_to_fix)} 个文件")

if __name__ == '__main__':
    main()
