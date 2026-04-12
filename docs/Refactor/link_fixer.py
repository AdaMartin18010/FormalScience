#!/usr/bin/env python3
"""
断链自动修复工具
基于扫描报告修复docs/Refactor/目录下的内部链接错误
"""

import os
import re
import json
from pathlib import Path
from collections import defaultdict

DOCS_ROOT = Path("e:/_src/FormalScience/docs/Refactor")
REPORT_PATH = DOCS_ROOT / "link_scan_report.json"

# 旧目录映射到新目录（根据文件名和内容推测）
DIR_MAPPING = {
    # 根目录下的旧结构
    "01_基础理论": "01_数学基础",
    "01_基础理论/01_命题逻辑基础": "01_数学基础/01_元数学基础/01.2_数理逻辑",
    "01_基础理论/02_类型论入门": "02_形式语言/02_类型论/02.1_简单类型论",
    "01_基础理论/03_依赖类型": "02_形式语言/02_类型论/02.3_依赖类型",
    "01_基础理论/04_归纳族与归纳原理": "01_数学基础/01_元数学基础/01.3_证明论基础",
    "01_基础理论/05_类型类系统": "03_编程范式/02_Rust语言深入/02.2_类型系统",
    "01_基础理论/06_Lambda演算": "02_形式语言/01_形式语言基础/01.3_λ演算",
    
    "02_实现技术": "examples",
    "02_实现技术/01_Lean语法速览": "examples/lean/README",
    "02_实现技术/02_证明策略": "06_调度系统/05_形式化证明/05.2_算法正确性证明",
    "02_实现技术/03_归纳证明模式": "01_数学基础/01_元数学基础/01.3_证明论基础",
    "02_实现技术/05_效应处理": "03_编程范式/03_异步编程模型",
    
    "03_应用领域": "06_调度系统",
    "03_应用领域/01_调度理论": "06_调度系统/01_调度理论基础",
    "03_应用领域/01_调度理论/00_概述": "06_调度系统/README",
    "03_应用领域/01_调度理论/03_高级性质证明": "06_调度系统/05_形式化证明/05.5_高级主题证明",
    "03_应用领域/02_程序分析": "04_软件工程",
    "03_应用领域/03_并发系统": "04_软件工程/04_分布式系统",
    "03_应用领域/04_硬件验证": "06_调度系统/02_硬件调度",
    
    "04_工具链": "tools",
    "04_工具链/01_环境搭建": "tools/README",
    
    "05_案例研究": "cases",
    "05_案例研究/01_简单证明示例": "01_数学基础/01_元数学基础/01.3_证明论基础",
    "05_案例研究/02_中等复杂度证明": "06_调度系统/05_形式化证明/05.4_调度等价性与复杂度证明",
    
    "06_参考手册": "quickref",
    "06_参考手册/03_元编程指南": "tools",
    
    "07_交叉视角/01_范畴论视角": "07_交叉视角/01_形式化方法统一/01.2_范畴论统一视角",
    "07_交叉视角/02_类型系统比较": "02_形式语言/02_类型论/02.1_简单类型系统",
}

# 文件映射（精确匹配）
FILE_MAPPING = {
    "Git指南.md": "CONTRIBUTING.md",
    "MIGRATION_v2_to_v3.md": "CHANGELOG.md",
    "TRADEMARKS.md": "LICENSE.md",
}

def load_report():
    """加载扫描报告"""
    with open(REPORT_PATH, 'r', encoding='utf-8') as f:
        return json.load(f)

def find_actual_file(target_name, source_file):
    """根据目标文件名查找实际存在的文件"""
    # 如果文件名在映射中，直接返回
    if target_name in FILE_MAPPING:
        mapped = FILE_MAPPING[target_name]
        mapped_path = DOCS_ROOT / mapped
        if mapped_path.exists():
            return mapped_path
    
    # 搜索所有可能的文件
    target_base = Path(target_name).stem
    for md_file in DOCS_ROOT.rglob("*.md"):
        if md_file.stem == target_base or md_file.name == target_name:
            return md_file
    
    return None

def fix_path(url, source_file):
    """修复单个链接路径"""
    if not url:
        return url, False
    
    # 跳过外部链接和纯锚点
    if url.startswith(('http://', 'https://', 'ftp://', 'mailto:', '#')):
        return url, False
    
    original_url = url
    
    # 分离锚点
    anchor = ""
    if '#' in url:
        url, anchor = url.split('#', 1)
        anchor = '#' + anchor
    
    # 检查是否是目录链接（以/结尾）
    is_dir = url.endswith('/')
    if is_dir:
        url = url.rstrip('/')
    
    # 尝试精确映射
    if url in DIR_MAPPING:
        new_url = DIR_MAPPING[url]
        if is_dir:
            new_url = new_url + '/'
        return new_url + anchor, True
    
    # 尝试文件映射
    url_name = Path(url).name
    if url_name in FILE_MAPPING:
        new_url = str(Path(url).parent / FILE_MAPPING[url_name])
        if is_dir:
            new_url = new_url + '/'
        return new_url + anchor, True
    
    # 修复相对路径问题：如果路径中包含"01_数学基础"等，但从子目录引用
    # 需要检查是否是绝对路径引用问题
    source_rel = source_file.relative_to(DOCS_ROOT)
    source_parts = list(source_rel.parent.parts)
    
    # 如果URL以./01_开头，可能是错误的绝对引用
    url_parts = url.strip('./').split('/')
    
    # 检查是否是"./01_数学基础/01_元数学基础/..."从"01_数学基础/01_元数学基础"内部引用
    if len(url_parts) >= 2 and url_parts[0] in ['01_数学基础', '02_形式语言', '03_编程范式', '04_软件工程', '05_形式化理论', '06_调度系统', '07_交叉视角', '08_附录', '09_统计学', '10_信息论', '11_系统科学', '12_决策与博弈论', '13_认知科学形式模型', '14_形式语言学', '15_社会科学形式化']:
        # 检查当前文件是否已经在该目录下
        if len(source_parts) >= 1 and source_parts[0] == url_parts[0]:
            # 需要从根目录的引用改为相对引用
            # 计算正确的相对路径
            remaining_parts = url_parts[1:]  # 去掉根目录部分
            
            # 从source_file.parent开始算
            if len(source_parts) == 1:
                # 直接在根目录下
                new_url = './' + '/'.join(remaining_parts)
            else:
                # 需要向上返回
                up_levels = len(source_parts) - 1
                new_url = '../' * up_levels + '/'.join(remaining_parts)
            
            if is_dir:
                new_url = new_url + '/'
            return new_url + anchor, True
    
    # 修复跨目录的../引用问题
    if url.startswith('../'):
        # 检查目标是否存在
        target = (source_file.parent / url).resolve()
        if not target.exists():
            # 尝试从根目录查找
            url_without_prefix = url.lstrip('../').lstrip('./')
            root_target = DOCS_ROOT / url_without_prefix
            if root_target.exists():
                # 重新计算正确的相对路径
                try:
                    rel_path = root_target.relative_to(source_file.parent)
                    new_url = str(rel_path).replace('\\', '/')
                    if is_dir:
                        new_url = new_url + '/'
                    return new_url + anchor, True
                except ValueError:
                    # 文件不在子路径中，跳过
                    pass
    
    # 检查是否是examples/lean等路径问题
    if 'examples/' in url or url.endswith('.lean'):
        # 这是一个示例文件引用，检查是否存在
        target = (source_file.parent / url).resolve()
        if not target.exists():
            # 尝试找到正确的路径
            file_name = Path(url).name
            for f in DOCS_ROOT.rglob(file_name):
                if f.exists():
                    try:
                        rel_path = f.relative_to(source_file.parent)
                        return str(rel_path).replace('\\', '/'), True
                    except ValueError:
                        # 文件不在子路径中，返回None表示无法自动修复
                        return original_url + anchor, False
    
    # 未修复
    if is_dir:
        url = url + '/'
    return url + anchor, False

def fix_file_links(file_path, broken_links_in_file):
    """修复单个文件中的所有断链"""
    try:
        content = file_path.read_text(encoding='utf-8')
    except Exception as e:
        print(f"  无法读取文件 {file_path}: {e}")
        return 0, 0
    
    original_content = content
    fixed_count = 0
    not_fixed = []
    
    # 按位置倒序排序，这样替换不会影响后面的位置
    broken_links_in_file.sort(key=lambda x: x['line'], reverse=True)
    
    lines = content.split('\n')
    modified_lines = []
    
    for line_num, line in enumerate(lines, 1):
        # 找到这一行的所有断链
        line_broken = [b for b in broken_links_in_file if b['line'] == line_num]
        if not line_broken:
            modified_lines.append(line)
            continue
        
        modified_line = line
        for broken in line_broken:
            old_url = broken['url']
            new_url, was_fixed = fix_path(old_url, file_path)
            
            if was_fixed:
                # 替换链接
                old_pattern = f']({old_url})'
                new_pattern = f']({new_url})'
                if old_pattern in modified_line:
                    modified_line = modified_line.replace(old_pattern, new_pattern, 1)
                    fixed_count += 1
                    print(f"  行 {line_num}: [{broken['text']}]({old_url}) -> [{broken['text']}]({new_url})")
                else:
                    # 可能是锚点或其他格式，尝试更灵活的匹配
                    pattern = re.escape(f']({old_url}')
                    if re.search(pattern, modified_line):
                        modified_line = re.sub(pattern, f']({new_url}', modified_line, count=1)
                        fixed_count += 1
                        print(f"  行 {line_num}: [{broken['text']}]({old_url}) -> [{broken['text']}]({new_url})")
                    else:
                        not_fixed.append(broken)
            else:
                not_fixed.append(broken)
        
        modified_lines.append(modified_line)
    
    new_content = '\n'.join(modified_lines)
    
    if new_content != original_content:
        file_path.write_text(new_content, encoding='utf-8')
        print(f"  已保存: {file_path.relative_to(DOCS_ROOT)}")
    
    return fixed_count, len(not_fixed)

def main():
    print("=" * 70)
    print("断链自动修复工具")
    print("=" * 70)
    
    report = load_report()
    broken_links = report['broken_links']
    
    print(f"\n总断链数: {len(broken_links)}")
    
    # 按文件分组
    by_file = defaultdict(list)
    for link in broken_links:
        source_path = DOCS_ROOT / link['source']
        by_file[source_path].append(link)
    
    print(f"涉及文件数: {len(by_file)}")
    print("\n" + "=" * 70)
    print("开始修复...")
    print("=" * 70)
    
    total_fixed = 0
    total_not_fixed = 0
    not_fixed_list = []
    
    for file_path, links in sorted(by_file.items()):
        if not file_path.exists():
            print(f"\n[!] 源文件不存在: {file_path}")
            continue
        
        print(f"\n处理: {file_path.relative_to(DOCS_ROOT)}")
        fixed, not_fixed = fix_file_links(file_path, links)
        total_fixed += fixed
        total_not_fixed += not_fixed
        
        for nf in links[fixed:]:  # 记录未修复的
            not_fixed_list.append(nf)
    
    print("\n" + "=" * 70)
    print("修复完成!")
    print("=" * 70)
    print(f"已修复链接: {total_fixed}")
    print(f"无法修复: {total_not_fixed}")
    
    # 保存未修复列表
    if not_fixed_list:
        not_fixed_path = DOCS_ROOT / "not_fixed_links.json"
        with open(not_fixed_path, 'w', encoding='utf-8') as f:
            json.dump(not_fixed_list, f, ensure_ascii=False, indent=2)
        print(f"\n未修复链接列表已保存: {not_fixed_path}")

if __name__ == '__main__':
    main()
