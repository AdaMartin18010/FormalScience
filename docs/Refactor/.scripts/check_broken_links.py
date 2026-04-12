#!/usr/bin/env python3
"""
检查并修复文档中的断链
"""

import re
from pathlib import Path
from typing import Set, List, Tuple

DOCS_ROOT = Path("docs/Refactor")

# 需要扫描的主要章节目录
MAIN_SECTIONS = [
    "01_数学基础",
    "02_形式语言", 
    "03_编程范式",
    "04_软件工程",
    "05_形式化理论",
    "06_调度系统",
    "07_交叉视角",
    "09_统计学",
    "10_信息论",
    "11_系统科学",
    "12_决策与博弈论",
    "13_认知科学形式模型",
    "14_形式语言学",
    "15_社会科学形式化",
]

def get_all_md_files() -> Set[Path]:
    """获取所有markdown文件的路径集合"""
    md_files = set()
    for section in MAIN_SECTIONS:
        section_path = DOCS_ROOT / section
        if section_path.exists():
            for f in section_path.rglob("*.md"):
                md_files.add(f.relative_to(DOCS_ROOT))
    return md_files

def extract_links(content: str) -> List[Tuple[str, str]]:
    """提取markdown内容中的所有链接 [text](url)"""
    pattern = r'\[([^\]]+)\]\(([^)]+)\)'
    return re.findall(pattern, content)

def is_internal_link(url: str) -> bool:
    """判断是否为内部链接"""
    # 排除外部URL和锚点链接
    return not (
        url.startswith('http://') or 
        url.startswith('https://') or
        url.startswith('#') or
        url.startswith('mailto:')
    )

def resolve_link(link_path: str, current_file: Path) -> Path:
    """解析相对链接为相对于DOCS_ROOT的路径"""
    current_dir = current_file.parent
    
    # 处理 ./ 和 ../ 路径
    if link_path.startswith('./') or link_path.startswith('../'):
        resolved = (current_dir / link_path).resolve()
        try:
            return resolved.relative_to(DOCS_ROOT.resolve())
        except ValueError:
            return None
    elif link_path.startswith('/'):
        # 绝对路径（相对于docs root）
        return Path(link_path.lstrip('/'))
    else:
        # 同目录文件
        return current_dir.relative_to(DOCS_ROOT) / link_path

def check_broken_links():
    """检查所有文档中的断链"""
    all_files = get_all_md_files()
    print(f"找到 {len(all_files)} 个文档文件\n")
    
    broken_links = []
    checked = 0
    
    for section in MAIN_SECTIONS:
        section_path = DOCS_ROOT / section
        if not section_path.exists():
            continue
            
        for doc_path in section_path.rglob("*.md"):
            checked += 1
            rel_path = doc_path.relative_to(DOCS_ROOT)
            
            try:
                with open(doc_path, 'r', encoding='utf-8') as f:
                    content = f.read()
                
                links = extract_links(content)
                for text, url in links:
                    if not is_internal_link(url):
                        continue
                    
                    # 移除URL中的锚点部分
                    clean_url = url.split('#')[0]
                    if not clean_url:
                        continue
                    
                    resolved = resolve_link(clean_url, doc_path)
                    if resolved and resolved not in all_files:
                        broken_links.append({
                            'file': str(rel_path),
                            'text': text,
                            'url': url,
                            'resolved': str(resolved) if resolved else None
                        })
            except Exception as e:
                print(f"  错误读取 {rel_path}: {e}")
    
    print(f"检查了 {checked} 个文档\n")
    
    if broken_links:
        print(f"发现 {len(broken_links)} 个断链:\n")
        # 按文件分组
        by_file = {}
        for link in broken_links:
            f = link['file']
            if f not in by_file:
                by_file[f] = []
            by_file[f].append(link)
        
        for f, links in sorted(by_file.items()):
            print(f"{f}:")
            for link in links:
                print(f"  - [{link['text']}]({link['url']})")
                if link['resolved']:
                    print(f"    解析路径: {link['resolved']}")
    else:
        print("✓ 未发现断链！")
    
    return broken_links

if __name__ == "__main__":
    check_broken_links()
