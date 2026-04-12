#!/usr/bin/env python3
"""
断链自动修复工具 V2 - 处理根目录文件的旧结构链接
"""

import os
import re
import json
from pathlib import Path
from collections import defaultdict

DOCS_ROOT = Path("e:/_src/FormalScience/docs/Refactor")
REPORT_PATH = DOCS_ROOT / "link_scan_report.json"

# 增强的目录映射
DIR_MAPPING = {
    # 根目录旧结构映射
    "./01_基础理论/": "./01_数学基础/",
    "./02_实现技术/": "./examples/",
    "./03_应用领域/": "./06_调度系统/",
    "./04_工具链/": "./tools/",
    "./05_案例研究/": "./cases/",
    "./06_参考手册/": "./quickref/",
    
    # 具体文件映射
    "./01_基础理论/01_命题逻辑基础.md": "./01_数学基础/01_元数学基础/01.2_数理逻辑.md",
    "./01_基础理论/02_类型论入门.md": "./02_形式语言/02_类型论/02.1_简单类型论.md",
    "./01_基础理论/03_依赖类型.md": "./02_形式语言/02_类型论/02.3_依赖类型.md",
    "./01_基础理论/04_归纳族与归纳原理.md": "./01_数学基础/01_元数学基础/01.3_证明论基础.md",
    "./01_基础理论/05_类型类系统.md": "./03_编程范式/02_Rust语言深入/02.2_类型系统.md",
    "./01_基础理论/06_Lambda演算.md": "./02_形式语言/01_形式语言基础/01.3_λ演算.md",
    
    "./02_实现技术/01_Lean语法速览.md": "./examples/lean/README.md",
    "./02_实现技术/02_证明策略.md": "./06_调度系统/05_形式化证明/05.2_算法正确性证明.md",
    "./02_实现技术/03_归纳证明模式.md": "./01_数学基础/01_元数学基础/01.3_证明论基础.md",
    "./02_实现技术/05_效应处理.md": "./03_编程范式/03_异步编程模型/03.1_异步编程基础.md",
    
    "./03_应用领域/01_调度理论/": "./06_调度系统/01_调度理论基础/",
    "./03_应用领域/01_调度理论/00_概述.md": "./06_调度系统/README.md",
    "./03_应用领域/01_调度理论/03_高级性质证明.md": "./06_调度系统/05_形式化证明/05.5_高级主题证明.md",
    "./03_应用领域/02_程序分析/": "./04_软件工程/",
    "./03_应用领域/03_并发系统/": "./04_软件工程/04_分布式系统/",
    "./03_应用领域/04_硬件验证/": "./06_调度系统/02_硬件调度/",
    
    "./04_工具链/01_环境搭建.md": "./tools/README.md",
    
    "./05_案例研究/": "./cases/",
    "./05_案例研究/01_简单证明示例.md": "./01_数学基础/01_元数学基础/01.3_证明论基础.md",
    "./05_案例研究/02_中等复杂度证明.md": "./06_调度系统/05_形式化证明/05.4_调度等价性与复杂度证明.md",
    
    "./06_参考手册/03_元编程指南.md": "./tools/README.md",
    
    "./07_交叉视角/01_范畴论视角.md": "./07_交叉视角/01_形式化方法统一/01.2_范畴论统一视角.md",
    "./07_交叉视角/02_类型系统比较.md": "./02_形式语言/02_类型论/02.1_简单类型系统.md",
}

def load_report():
    with open(REPORT_PATH, 'r', encoding='utf-8') as f:
        return json.load(f)

def fix_url(url, source_file):
    """修复URL"""
    if not url or url.startswith(('http://', 'https://', 'ftp://', 'mailto:', '#')):
        return url, False
    
    original_url = url
    
    # 分离锚点
    anchor = ""
    if '#' in url:
        url, anchor = url.split('#', 1)
        anchor = '#' + anchor
    
    # 检查是否是目录链接
    is_dir = url.endswith('/')
    url_for_mapping = url
    if is_dir:
        url_for_mapping = url + '/'
    
    # 检查精确映射
    if url in DIR_MAPPING:
        new_url = DIR_MAPPING[url] + anchor
        return new_url, True
    
    # 尝试部分匹配（替换目录前缀）
    for old_prefix, new_prefix in sorted(DIR_MAPPING.items(), key=lambda x: -len(x[0])):
        if url.startswith(old_prefix.rstrip('/')):
            new_url = url.replace(old_prefix.rstrip('/'), new_prefix.rstrip('/'), 1) + anchor
            return new_url, True
    
    return original_url + anchor, False

def fix_file(file_path, links):
    """修复文件中的链接"""
    try:
        content = file_path.read_text(encoding='utf-8')
    except Exception as e:
        print(f"  [!] 无法读取: {e}")
        return 0
    
    original_content = content
    fixed_count = 0
    
    # 按行号倒序排序
    links.sort(key=lambda x: x['line'], reverse=True)
    
    lines = content.split('\n')
    modified = False
    
    for link in links:
        line_num = link['line'] - 1
        if line_num < 0 or line_num >= len(lines):
            continue
        
        line = lines[line_num]
        old_url = link['url']
        new_url, was_fixed = fix_url(old_url, file_path)
        
        if was_fixed:
            # 替换链接
            old_pattern = f']({old_url})'
            new_pattern = f']({new_url})'
            if old_pattern in line:
                line = line.replace(old_pattern, new_pattern, 1)
                lines[line_num] = line
                fixed_count += 1
                modified = True
                print(f"  行 {link['line']}: [{link['text']}]({old_url}) -> [{link['text']}]({new_url})")
    
    if modified:
        new_content = '\n'.join(lines)
        file_path.write_text(new_content, encoding='utf-8')
        print(f"  已保存: {file_path.relative_to(DOCS_ROOT)}")
    
    return fixed_count

def main():
    print("=" * 70)
    print("断链自动修复工具 V2")
    print("=" * 70)
    
    report = load_report()
    broken_links = report['broken_links']
    
    # 只处理根目录下的文件（路径中不包含/的）
    root_files = [l for l in broken_links if '/' not in l['source']]
    
    print(f"\n总断链数: {len(broken_links)}")
    print(f"根目录文件断链: {len(root_files)}")
    
    # 按文件分组
    by_file = defaultdict(list)
    for link in root_files:
        source_path = DOCS_ROOT / link['source']
        by_file[source_path].append(link)
    
    print(f"涉及根目录文件数: {len(by_file)}")
    print("\n" + "=" * 70)
    print("开始修复根目录文件...")
    print("=" * 70)
    
    total_fixed = 0
    
    for file_path, links in sorted(by_file.items()):
        if not file_path.exists():
            continue
        
        print(f"\n处理: {file_path.relative_to(DOCS_ROOT)}")
        fixed = fix_file(file_path, links)
        total_fixed += fixed
    
    print("\n" + "=" * 70)
    print("修复完成!")
    print("=" * 70)
    print(f"已修复链接: {total_fixed}")

if __name__ == '__main__':
    main()
