#!/usr/bin/env python3
"""
断链检测与修复工具
扫描docs/Refactor/目录下所有Markdown文件中的内部链接
"""

import os
import re
import json
from pathlib import Path
from collections import defaultdict
from urllib.parse import urlparse, unquote

DOCS_ROOT = Path("e:/_src/FormalScience/docs/Refactor")

def find_all_md_files():
    """查找所有Markdown文件"""
    md_files = []
    for root, dirs, files in os.walk(DOCS_ROOT):
        # 跳过隐藏目录
        dirs[:] = [d for d in dirs if not d.startswith('.')]
        for f in files:
            if f.endswith('.md'):
                md_files.append(Path(root) / f)
    return md_files

def extract_links(content, file_path):
    """提取Markdown中的链接"""
    links = []
    
    # 匹配 [text](url) 格式
    link_pattern = r'\[([^\]]+)\]\(([^\)]+)\)'
    matches = re.finditer(link_pattern, content, re.MULTILINE)
    
    for match in matches:
        text = match.group(1)
        url = match.group(2)
        
        # 忽略外部链接
        if url.startswith(('http://', 'https://', 'ftp://', 'mailto:')):
            continue
        
        # 忽略纯锚点（已经在当前文件中）
        if url.startswith('#'):
            links.append({
                'type': 'anchor',
                'text': text,
                'url': url,
                'line': content[:match.start()].count('\n') + 1,
                'pos': match.start()
            })
            continue
            
        # 解析相对路径
        links.append({
            'type': 'relative',
            'text': text,
            'url': url,
            'line': content[:match.start()].count('\n') + 1,
            'pos': match.start()
        })
    
    return links

def resolve_link(link, source_file):
    """解析链接为目标文件路径"""
    url = link['url']
    
    # 分离路径和锚点
    if '#' in url:
        path_part, anchor = url.split('#', 1)
        anchor = '#' + anchor
    else:
        path_part = url
        anchor = ''
    
    # URL解码
    path_part = unquote(path_part)
    
    # 如果是空路径（纯锚点）
    if not path_part:
        return source_file, anchor
    
    # 解析相对路径
    if path_part.startswith('/'):
        # 绝对路径（相对于docs/Refactor）
        target = DOCS_ROOT / path_part.lstrip('/')
    else:
        # 相对路径
        target = source_file.parent / path_part
    
    # 规范化路径
    target = target.resolve()
    
    return target, anchor

def check_anchor_exists(target_file, anchor):
    """检查锚点是否存在于文件中"""
    if not anchor:
        return True
    
    anchor_id = anchor.lstrip('#')
    
    try:
        content = target_file.read_text(encoding='utf-8')
    except:
        return False
    
    # 查找标题锚点
    # Markdown标题: ## Title {#anchor} 或 ## Title
    header_patterns = [
        rf'{{#{re.escape(anchor_id)}}}',
        rf'\[.*?\]\(#{re.escape(anchor_id)}\)',
        rf'^#+ .*?{{#{re.escape(anchor_id)}}}',
        rf'\s#{re.escape(anchor_id)}\s*$',
        rf'name=["\']{re.escape(anchor_id)}["\']',
        rf'id=["\']{re.escape(anchor_id)}["\']',
    ]
    
    for pattern in header_patterns:
        if re.search(pattern, content, re.MULTILINE | re.IGNORECASE):
            return True
    
    # 检查是否作为标题ID存在
    # 标准Markdown标题生成锚点
    headers = re.findall(r'^#+ (.+)$', content, re.MULTILINE)
    for header in headers:
        # 生成GitHub风格的锚点ID
        anchor_candidate = header.lower().strip()
        anchor_candidate = re.sub(r'[^\w\s-]', '', anchor_candidate)
        anchor_candidate = re.sub(r'\s+', '-', anchor_candidate)
        if anchor_candidate == anchor_id:
            return True
    
    return False

def check_link(link, source_file):
    """验证单个链接"""
    target_file, anchor = resolve_link(link, source_file)
    
    result = {
        'link': link,
        'source': source_file,
        'target_file': target_file,
        'anchor': anchor,
        'exists': False,
        'anchor_valid': False,
        'issue': None
    }
    
    # 检查文件是否存在
    if target_file.exists():
        result['exists'] = True
        # 检查是否是文件（不是目录）
        if target_file.is_file():
            result['anchor_valid'] = check_anchor_exists(target_file, anchor)
            if not result['anchor_valid'] and anchor:
                result['issue'] = 'anchor_not_found'
        else:
            result['exists'] = False
            result['issue'] = 'is_directory'
    else:
        result['issue'] = 'file_not_found'
    
    return result

def scan_all_links():
    """扫描所有链接"""
    md_files = find_all_md_files()
    print(f"找到 {len(md_files)} 个Markdown文件")
    
    all_links = []
    broken_links = []
    
    for md_file in md_files:
        try:
            content = md_file.read_text(encoding='utf-8')
            links = extract_links(content, md_file)
            
            for link in links:
                all_links.append({
                    'file': md_file,
                    'link': link
                })
                
                # 验证链接
                result = check_link(link, md_file)
                if result['issue']:
                    broken_links.append(result)
        except Exception as e:
            print(f"错误处理文件 {md_file}: {e}")
    
    return all_links, broken_links, md_files

def find_similar_files(target_name, all_files):
    """查找相似文件名作为建议"""
    from difflib import get_close_matches
    
    all_names = [f.name for f in all_files]
    # 去掉.md后缀进行比较
    base_name = target_name
    if target_name.endswith('.md'):
        base_name = target_name[:-3]
    
    matches = get_close_matches(target_name, all_names, n=3, cutoff=0.6)
    return matches

def generate_fix_suggestion(broken, all_files):
    """生成修复建议"""
    target = broken['target_file']
    url = broken['link']['url']
    source = broken['source']
    
    # 尝试找到可能的正确路径
    suggestions = []
    
    # 检查是否是简单的文件名不匹配
    target_name = target.name
    similar = find_similar_files(target_name, all_files)
    
    for sim in similar:
        # 找到相似文件的完整路径
        for f in all_files:
            if f.name == sim:
                try:
                    rel_path = f.relative_to(source.parent)
                    suggestions.append(str(rel_path).replace('\\', '/'))
                except ValueError:
                    # 文件不在同一子路径下，使用相对于根目录的路径
                    try:
                        rel_path = f.relative_to(DOCS_ROOT)
                        suggestions.append(str(rel_path).replace('\\', '/'))
                    except ValueError:
                        pass
                break
    
    return suggestions

def main():
    print("=" * 60)
    print("断链扫描工具 - 开始扫描")
    print("=" * 60)
    
    all_links, broken_links, all_files = scan_all_links()
    
    print(f"\n总链接数: {len(all_links)}")
    print(f"断链数量: {len(broken_links)}")
    
    # 按问题类型分类
    by_issue = defaultdict(list)
    for broken in broken_links:
        by_issue[broken['issue']].append(broken)
    
    print("\n" + "=" * 60)
    print("断链分类统计")
    print("=" * 60)
    
    for issue, items in sorted(by_issue.items()):
        print(f"  {issue}: {len(items)} 个")
    
    # 生成详细报告
    report = {
        'summary': {
            'total_files': len(all_files),
            'total_links': len(all_links),
            'broken_count': len(broken_links),
            'by_issue': {k: len(v) for k, v in by_issue.items()}
        },
        'broken_links': []
    }
    
    print("\n" + "=" * 60)
    print("详细断链列表")
    print("=" * 60)
    
    for broken in broken_links:
        source_rel = broken['source'].relative_to(DOCS_ROOT)
        target_rel = broken['target_file'].relative_to(DOCS_ROOT) if broken['target_file'].is_relative_to(DOCS_ROOT) else broken['target_file']
        
        entry = {
            'source': str(source_rel).replace('\\', '/'),
            'target': str(target_rel).replace('\\', '/'),
            'url': broken['link']['url'],
            'text': broken['link']['text'],
            'line': broken['link']['line'],
            'issue': broken['issue'],
            'suggestions': generate_fix_suggestion(broken, all_files)
        }
        report['broken_links'].append(entry)
        
        print(f"\n来源: {source_rel}")
        print(f"  行号: {broken['link']['line']}")
        print(f"  链接文本: {broken['link']['text']}")
        print(f"  链接URL: {broken['link']['url']}")
        print(f"  目标: {target_rel}")
        print(f"  问题: {broken['issue']}")
        if entry['suggestions']:
            print(f"  建议: {', '.join(entry['suggestions'])}")
    
    # 保存报告
    report_path = DOCS_ROOT / 'link_scan_report.json'
    with open(report_path, 'w', encoding='utf-8') as f:
        json.dump(report, f, ensure_ascii=False, indent=2)
    
    print(f"\n{'=' * 60}")
    print(f"报告已保存: {report_path}")
    print("=" * 60)
    
    return report

if __name__ == '__main__':
    main()
