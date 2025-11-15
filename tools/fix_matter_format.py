#!/usr/bin/env python3
"""
统一 Matter 文件夹中所有 Markdown 文件的格式
- 统一目录格式
- 统一标题编号格式
- 保持序号结构一致性
"""

import os
import re
import unicodedata
from pathlib import Path
from typing import List, Tuple, Dict, Optional

def slugify(text: str) -> str:
    """生成 GitHub 风格的锚点 ID"""
    # 转换为小写
    text = text.lower()
    # 移除编号前缀（用于生成锚点）
    text = re.sub(r'^\d+[\.、]?\s*', '', text)
    # Unicode 规范化
    text = unicodedata.normalize('NFKD', text)
    # 移除特殊字符，保留中文、英文、数字、空格、连字符
    text = re.sub(r'[^\w\s\u4e00-\u9fff-]', '', text)
    # 将空格和多个连字符替换为单个连字符
    text = re.sub(r'[-\s]+', '-', text)
    # 移除首尾连字符
    text = text.strip('-')
    return text

def extract_headers(content: str) -> List[Tuple[int, str]]:
    """提取所有标题，返回 (级别, 原始文本)"""
    headers = []
    lines = content.split('\n')
    
    for line in lines:
        # 匹配 Markdown 标题
        match = re.match(r'^(#{1,6})\s+(.+)$', line)
        if match:
            level = len(match.group(1))
            text = match.group(2).strip()
            # 跳过"目录"标题，它不应该被编号
            if text.strip() in ['目录', '📋 目录', '目录 📋']:
                continue
            headers.append((level, text))
    
    return headers

def normalize_header_numbering(headers: List[Tuple[int, str]]) -> List[Tuple[int, str, str]]:
    """规范化标题编号，返回 (级别, 原始文本, 新编号文本)"""
    if not headers:
        return []
    
    normalized = []
    counters = {1: 0, 2: 0, 3: 0, 4: 0, 5: 0, 6: 0}
    last_level = 0
    
    for level, text in headers:
        # 移除现有的编号，但保留内容
        text_clean = text.strip()
        # 移除数字编号（如 "1. ", "1.1 ", "1.1.1 " 等）
        text_clean = re.sub(r'^\d+(?:\.\d+)*[\.、]?\s*', '', text_clean)
        # 移除中文编号（如 "第一部分", "第一章" 等）
        text_clean = re.sub(r'^第[一二三四五六七八九十百千万]+[部分章节]\s*', '', text_clean)
        text_clean = text_clean.strip()
        
        # 如果清理后为空，使用原始文本
        if not text_clean:
            text_clean = text.strip()
        
        # 更新计数器
        if level <= last_level:
            # 重置下级计数器
            for l in range(level + 1, 7):
                counters[l] = 0
        
        counters[level] += 1
        last_level = level
        
        # 生成新编号
        if level == 1:
            new_text = f"{counters[1]}. {text_clean}"
        elif level == 2:
            new_text = f"{counters[1]}.{counters[2]} {text_clean}"
        elif level == 3:
            new_text = f"{counters[1]}.{counters[2]}.{counters[3]} {text_clean}"
        elif level == 4:
            new_text = f"{counters[1]}.{counters[2]}.{counters[3]}.{counters[4]} {text_clean}"
        elif level == 5:
            new_text = f"{counters[1]}.{counters[2]}.{counters[3]}.{counters[4]}.{counters[5]} {text_clean}"
        else:
            new_text = f"{counters[1]}.{counters[2]}.{counters[3]}.{counters[4]}.{counters[5]}.{counters[6]} {text_clean}"
        
        normalized.append((level, text, new_text))
    
    return normalized

def generate_toc(headers: List[Tuple[int, str, str]]) -> str:
    """生成标准化的目录"""
    if not headers:
        return ""
    
    toc_lines = ["## 目录", ""]
    
    for level, original, new_text in headers:
        # 跳过"目录"标题本身
        text_clean = new_text.strip()
        if re.match(r'^\d+[\.、]?\s*目录', text_clean, re.IGNORECASE):
            continue
        
        indent = "  " * (level - 1)
        # 生成锚点
        anchor = slugify(new_text)
        toc_lines.append(f"{indent}- [{new_text}](#{anchor})")
    
    return "\n".join(toc_lines) + "\n"

def update_content_headers(content: str, header_mapping: Dict[str, str]) -> str:
    """更新内容中的标题"""
    lines = content.split('\n')
    result = []
    
    for line in lines:
        match = re.match(r'^(#{1,6})\s+(.+)$', line)
        if match:
            level = len(match.group(1))
            original_text = match.group(2).strip()
            
            # 跳过"目录"标题，保持为"## 目录"（不编号）
            # 检查是否是目录标题（可能已经编号）
            if (original_text.strip() in ['目录', '📋 目录', '目录 📋'] or 
                re.match(r'^\d+(?:\.\d+)*[\.、]?\s*[📋]*\s*目录', original_text, re.IGNORECASE)):
                result.append(f"{'#' * level} 目录")
            # 查找对应的新标题
            elif original_text in header_mapping:
                result.append(f"{'#' * level} {header_mapping[original_text]}")
            else:
                result.append(line)
        else:
            result.append(line)
    
    return '\n'.join(result)

def find_and_replace_toc(content: str, new_toc: str) -> str:
    """查找并替换目录"""
    # 匹配各种可能的目录格式
    # 匹配 ## 目录 或 ## 📋 目录 等
    toc_start_pattern = r'##\s*[📋]*\s*目录\s*\n'
    
    # 查找所有可能的目录位置
    toc_matches = list(re.finditer(toc_start_pattern, content, re.IGNORECASE | re.MULTILINE))
    
    if toc_matches:
        # 从第一个目录开始替换（通常第一个是正确的）
        for toc_match in toc_matches:
            start_pos = toc_match.start()
            # 查找目录结束位置
            remaining = content[start_pos + toc_match.end():]
            
            # 匹配目录内容（列表项，可能跨多行）
            # 匹配到下一个 ## 标题
            lines = remaining.split('\n')
            toc_end = 0
            found_list = False
            
            for i, line in enumerate(lines):
                # 如果是列表项
                if re.match(r'^(?:  )*(?:-|\*|\d+\.)\s*\[.*?\]\(.*?\)', line):
                    found_list = True
                    toc_end = i + 1
                # 如果遇到下一个 ## 标题
                elif line.strip().startswith('##'):
                    break
                # 如果已经找到列表项，遇到空行后还有非列表内容，停止
                elif found_list and line.strip() and not re.match(r'^(?:  )*(?:-|\*|\d+\.)', line):
                    break
                # 如果还没找到列表项，但遇到非列表内容，可能不是目录
                elif not found_list and line.strip() and not re.match(r'^(?:  )*(?:-|\*|\d+\.)', line):
                    break
                elif found_list:
                    # 继续收集列表项后的空行
                    toc_end = i + 1
            
            if found_list:
                # 找到目录内容，替换
                toc_content = '\n'.join(lines[:toc_end])
                end_pos = start_pos + toc_match.end() + len(toc_content)
                # 确保包含末尾的换行
                if end_pos < len(content) and content[end_pos] == '\n':
                    end_pos += 1
                # 替换第一个找到的目录，然后继续处理其他可能的旧目录
                content = content[:start_pos] + new_toc + content[end_pos:]
                # 继续查找并删除其他可能的旧目录
                break
            else:
                # 只找到目录标题，查找下一个 ## 标题
                next_header = re.search(r'\n##\s+', remaining)
                if next_header:
                    end_pos = start_pos + toc_match.end() + next_header.start()
                    return content[:start_pos] + new_toc + content[end_pos:]
                else:
                    # 没有下一个标题，替换到文件末尾
                    return content[:start_pos] + new_toc + remaining
        
        # 如果所有匹配都处理了，返回原内容（不应该到这里）
        return content
    else:
        # 没有找到目录，在第一个标题后插入
        first_header_match = re.search(r'^(#\s+.+)$', content, re.MULTILINE)
        if first_header_match:
            pos = first_header_match.end()
            # 查找是否已经有空行
            next_chars = content[pos:pos+2]
            if next_chars == '\n\n':
                return content[:pos+2] + new_toc + content[pos+2:]
            elif next_chars.startswith('\n'):
                return content[:pos+1] + '\n' + new_toc + content[pos+1:]
            else:
                return content[:pos] + '\n\n' + new_toc + content[pos:]
    
    return content

def fix_file(file_path: Path) -> bool:
    """修复单个文件的格式"""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
    except Exception as e:
        print(f"  读取文件失败: {e}")
        return False
    
    # 提取标题
    headers = extract_headers(content)
    
    if not headers:
        # 没有标题，跳过
        return False
    
    # 规范化编号
    normalized = normalize_header_numbering(headers)
    
    if not normalized:
        return False
    
    # 创建标题映射（原始文本 -> 新文本）
    header_mapping = {orig: new for _, orig, new in normalized}
    
    # 生成新目录
    new_toc = generate_toc(normalized)
    
    # 更新内容中的标题
    updated_content = update_content_headers(content, header_mapping)
    
    # 替换或插入目录
    updated_content = find_and_replace_toc(updated_content, new_toc)
    
    # 清理可能残留的旧目录（只删除编号的目录标题，不删除标准的"## 目录"）
    # 删除所有以 ## 数字. 目录 或 ## 数字 📋 目录 开头的块
    old_toc_pattern = r'##\s+\d+(?:\.\d+)*[\.、]?\s*[📋]*\s*目录\s*\n(?:(?:  )*(?:-|\*|\d+\.)\s*\[.*?\]\(.*?\)\s*\n?)+'
    updated_content = re.sub(old_toc_pattern, '', updated_content, flags=re.MULTILINE)
    
    # 写回文件
    try:
        with open(file_path, 'w', encoding='utf-8') as f:
            f.write(updated_content)
        return True
    except Exception as e:
        print(f"  写入文件失败: {e}")
        return False

def process_directory(root_dir: Path):
    """递归处理目录中的所有 Markdown 文件"""
    md_files = list(root_dir.rglob('*.md'))
    total = len(md_files)
    success = 0
    failed = []
    
    print(f"找到 {total} 个 Markdown 文件")
    
    for i, md_file in enumerate(md_files, 1):
        print(f"[{i}/{total}] 处理: {md_file.relative_to(root_dir)}")
        if fix_file(md_file):
            success += 1
        else:
            failed.append(md_file)
    
    print(f"\n处理完成: 成功 {success}/{total}")
    if failed:
        print(f"失败的文件 ({len(failed)}):")
        for f in failed:
            print(f"  - {f.relative_to(root_dir)}")

if __name__ == '__main__':
    # Matter 目录路径
    matter_dir = Path(__file__).parent.parent / 'docs' / 'Matter'
    
    if not matter_dir.exists():
        print(f"目录不存在: {matter_dir}")
        exit(1)
    
    print(f"开始处理目录: {matter_dir}")
    process_directory(matter_dir)
    print("完成！")
