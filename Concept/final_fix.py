#!/usr/bin/env python3
"""
最终修复：处理所有剩余的格式问题
1. 英文标题翻译
2. 章节编号格式（去掉空格）
3. 目录链接格式
"""

import os
import re
from pathlib import Path

# 扩展的标题翻译字典
TITLE_MAP = {
    'Philosophical Implications': '哲学意涵',
    'Historical 26 Stages Complete': '历史26阶段完整',
    'Future 26 Stages Roadmap': '未来26阶段路线图',
    'Human Computer Cognitive Fusion': '人机认知融合',
    'Reflexivity Paradigm Analysis': '反身性范式分析',
    'Social Structure Formal Language Perspective': '社会结构形式语言视角',
    'Economic Financial Formal Language Analysis': '经济金融形式语言分析',
    'Blockchain Formal Language Perspective': '区块链形式语言视角',
    'Time Complexity': '时间复杂度',
    'Industry Trends': '行业趋势',
    'Research Frontiers': '研究前沿',
    'Theoretical Limits': '理论极限',
    'Ecosystem Evolution': '生态系统演进',
    'Emerging Proposals': '新兴提案',
    'Migration Pathways': '迁移路径',
    'Scalability Patterns': '可扩展性模式',
    'Cost Benefit Analysis': '成本效益分析',
    'Deployment Strategies': '部署策略',
    'Performance Economics': '性能经济学',
    'Universal Computation': '通用计算',
    'Abstraction Layers': '抽象层',
    'Determinism Epistemology': '确定性认识论',
    'Security Philosophy': '安全哲学',
    'Portability Theory': '可移植性理论',
    'Blockchain Contracts': '区块链合约',
    'Plugin Systems': '插件系统',
    'Microservices': '微服务',
    'IoT Embedded': '物联网嵌入式',
    'Serverless Edge': '无服务器边缘',
    'Interoperability': '互操作性',
}

def extract_file_number(filename):
    """从文件名提取编号"""
    match = re.match(r'(\d+\.\d+)_', filename)
    return match.group(1) if match else None

def translate_title(title):
    """翻译标题"""
    # 先尝试完整匹配
    if title in TITLE_MAP:
        return TITLE_MAP[title]
    
    # 尝试部分匹配
    for en, zh in TITLE_MAP.items():
        if en in title:
            return title.replace(en, zh)
    
    return title

def fix_file(filepath):
    """修复单个文件的所有问题"""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
        
        original = content
        filename = Path(filepath).name
        file_number = extract_file_number(filename)
        
        if not file_number:
            return False
        
        # 1. 修复标题
        title_match = re.match(r'^# (\d+\.\d+) (.+)$', content, re.MULTILINE)
        if title_match:
            number = title_match.group(1).lstrip('0').lstrip('.')
            if not number:
                number = title_match.group(1)
            title_text = title_match.group(2)
            
            # 翻译标题
            translated = translate_title(title_text)
            new_title = f"# {number} {translated}"
            content = re.sub(r'^# .+$', new_title, content, count=1, flags=re.MULTILINE)
            
            # 2. 修复目录中的标题链接
            anchor = re.sub(r'[^\w\-]', '', f"{number} {translated}".lower().replace(' ', '-'))
            content = re.sub(
                r'- \[([^\]]+)\]\(#[^\)]+\)',
                lambda m: f"- [{number} {translated}](#{anchor})" if m.group(1).startswith(number) or 'Philosophical' in m.group(1) or 'Implications' in m.group(1) else m.group(0),
                content,
                count=1
            )
        
        # 3. 修复章节编号格式（去掉空格）
        content = re.sub(r'^## (\d+) \. ', r'## \1 ', content, flags=re.MULTILINE)
        content = re.sub(r'^### (\d+) \. ', r'### \1 ', content, flags=re.MULTILINE)
        content = re.sub(r'^#### (\d+) \. ', r'#### \1 ', content, flags=re.MULTILINE)
        
        # 4. 修复目录中的章节链接（去掉空格）
        content = re.sub(r'- \[(\d+) \. ([^\]]+)\]\(#\d+--', r'- [\1 \2](#\1-', content)
        
        if content != original:
            with open(filepath, 'w', encoding='utf-8') as f:
                f.write(content)
            return True
        return False
    except Exception as e:
        print(f"✗ 错误 {filepath}: {e}")
        return False

def main():
    base_dir = Path(__file__).parent
    pattern = re.compile(r'^\d+\.\d+_.+\.md$')
    files = []
    
    for root, dirs, filenames in os.walk(base_dir):
        if 'node_modules' in root or '.git' in root:
            continue
        for f in filenames:
            if pattern.match(f):
                files.append(Path(root) / f)
    
    print(f"检查 {len(files)} 个文件...\n")
    
    fixed = 0
    for filepath in sorted(files):
        if fix_file(filepath):
            print(f"✓ {filepath.name}")
            fixed += 1
    
    print(f"\n完成！修复了 {fixed}/{len(files)} 个文件")

if __name__ == '__main__':
    main()
