#!/usr/bin/env python3
"""
修复剩余的断链
"""

import os
import re
import json
from pathlib import Path
from collections import defaultdict

class RemainingLinkFixer:
    def __init__(self, base_path="."):
        self.base_path = Path(base_path).resolve()
        self.fixed_count = 0
        
    def load_broken_links(self, json_file="broken_links_data.json"):
        """加载断链数据"""
        with open(json_file, 'r', encoding='utf-8') as f:
            data = json.load(f)
        return data['broken_links']
        
    def fix_remaining_schedule_links(self, broken_links):
        """修复剩余的 schedule_formal_view.md 链接 - 改为指向 README.md 或移除锚点"""
        schedule_links = [l for l in broken_links 
                         if 'schedule_formal_view.md' in l['target'] 
                         and l['type'] == 'missing_file']
        
        by_source = defaultdict(list)
        for link in schedule_links:
            by_source[link['source']].append(link)
            
        for source, links in by_source.items():
            source_path = self.base_path / source
            if not source_path.exists():
                continue
                
            content = source_path.read_text(encoding='utf-8')
            original_content = content
            
            for link in links:
                old_target = link['target']
                # 将 schedule_formal_view.md 替换为 README.md
                if '#' in old_target:
                    # 有锚点的链接，移除锚点只保留文件
                    new_target = "README.md"
                else:
                    new_target = "README.md"
                    
                old_pattern = re.escape(f"]({old_target})")
                content = re.sub(old_pattern, f"]({new_target})", content)
                self.fixed_count += 1
                print(f"  ✓ 修复: {source} -> {new_target}")
                
            if content != original_content:
                source_path.write_text(content, encoding='utf-8')
                
    def fix_mindmap_anchors(self, broken_links):
        """修复思维导图文件中的锚点 - 添加缺失的锚点到对应标题"""
        mindmap_file = self.base_path / "Composed/schedule_formal_view/思维导图与知识矩阵.md"
        if not mindmap_file.exists():
            return
            
        # 获取所有缺失的锚点
        missing_anchors = {}
        for link in broken_links:
            if link['type'] == 'missing_anchor' and '思维导图与知识矩阵.md' in link['target']:
                anchor = link['target'].split('#')[-1]
                missing_anchors[anchor] = link
                
        if not missing_anchors:
            return
            
        print(f"  发现 {len(missing_anchors)} 个缺失锚点需要添加")
        
        content = mindmap_file.read_text(encoding='utf-8')
        original_content = content
        
        # 锚点到标题的映射
        anchor_patterns = {
            '31-01-cpu硬件层': (r'^(### 3\.1 01 CPU硬件层)\s*$', '### 3.1 01 CPU硬件层 {#' + '31-01-cpu硬件层' + '}'),
            '32-02-系统总线层': (r'^(### 3\.2 02 系统总线层)\s*$', '### 3.2 02 系统总线层 {#' + '32-02-系统总线层' + '}'),
            '33-03-os抽象层': (r'^(### 3\.3 03 OS抽象层)\s*$', '### 3.3 03 OS抽象层 {#' + '33-03-os抽象层' + '}'),
            '34-04-同步通信机制': (r'^(### 3\.4 04 同步通信机制)\s*$', '### 3.4 04 同步通信机制 {#' + '34-04-同步通信机制' + '}'),
            '35-05-虚拟化容器化沙盒化': (r'^(### 3\.5 05 虚拟化容器化沙盒化)\s*$', '### 3.5 05 虚拟化容器化沙盒化 {#' + '35-05-虚拟化容器化沙盒化' + '}'),
            '36-06-调度模型': (r'^(### 3\.6 06 调度模型)\s*$', '### 3.6 06 调度模型 {#' + '36-06-调度模型' + '}'),
            '37-07-性能优化与安全': (r'^(### 3\.7 07 性能优化与安全)\s*$', '### 3.7 07 性能优化与安全 {#' + '37-07-性能优化与安全' + '}'),
            '38-08-技术演进与对标': (r'^(### 3\.8 08 技术演进与对标)\s*$', '### 3.8 08 技术演进与对标 {#' + '38-08-技术演进与对标' + '}'),
            '39-09-形式化理论与证明': (r'^(### 3\.9 09 形式化理论与证明)\s*$', '### 3.9 09 形式化理论与证明 {#' + '39-09-形式化理论与证明' + '}'),
            '310-10-24-扩展主题': (r'^(### 3\.10 10-24 扩展主题)\s*$', '### 3.10 10-24 扩展主题 {#' + '310-10-24-扩展主题' + '}'),
        }
        
        for anchor, (pattern, replacement) in anchor_patterns.items():
            if anchor in missing_anchors:
                if re.search(pattern, content, re.MULTILINE):
                    content = re.sub(pattern, replacement, content, flags=re.MULTILINE)
                    self.fixed_count += 1
                    print(f"  ✓ 添加锚点: {anchor}")
                    
        if content != original_content:
            mindmap_file.write_text(content, encoding='utf-8')
            
    def fix_linux_principles_link(self, broken_links):
        """修复 LINUX_OS_PRINCIPLES.md 的链接 - 改为纯文本"""
        linux_links = [l for l in broken_links 
                      if 'LINUX_OS_PRINCIPLES.md' in l['target']]
        
        by_source = defaultdict(list)
        for link in linux_links:
            by_source[link['source']].append(link)
            
        for source, links in by_source.items():
            source_path = self.base_path / source
            if not source_path.exists():
                continue
                
            content = source_path.read_text(encoding='utf-8')
            original_content = content
            
            for link in links:
                old_target = link['target']
                link_text = link['link_text']
                # 将链接改为纯文本
                old_pattern = rf'\[{re.escape(link_text)}\]\({re.escape(old_target)}\)'
                content = re.sub(old_pattern, link_text, content)
                self.fixed_count += 1
                print(f"  ✓ 移除无效链接: {source} -> {old_target}")
                
            if content != original_content:
                source_path.write_text(content, encoding='utf-8')
                
    def create_schedule_formal_view_file(self):
        """创建 schedule_formal_view.md 作为主入口文件"""
        target_file = self.base_path / "Composed/schedule_formal_view/schedule_formal_view.md"
        if target_file.exists():
            return
            
        # 创建指向README的重定向文件
        content = """---
title: "调度形式化视角"
status: "重定向"
---

# 调度形式化视角

此文档已合并至 [README.md](./README.md)

请查看 [README.md](./README.md) 获取完整内容。
"""
        target_file.write_text(content, encoding='utf-8')
        print(f"  ✓ 创建: {target_file.relative_to(self.base_path)}")
        self.fixed_count += 1
        
    def run_all_fixes(self):
        """运行所有修复"""
        print("=" * 60)
        print("修复剩余断链")
        print("=" * 60)
        
        broken_links = self.load_broken_links()
        print(f"\n加载了 {len(broken_links)} 个断链记录")
        
        print("\n1. 创建 schedule_formal_view.md 重定向文件...")
        self.create_schedule_formal_view_file()
        
        print("\n2. 修复剩余的 schedule_formal_view.md 链接...")
        self.fix_remaining_schedule_links(broken_links)
        
        print("\n3. 修复思维导图锚点...")
        self.fix_mindmap_anchors(broken_links)
        
        print("\n4. 修复 LINUX_OS_PRINCIPLES.md 链接...")
        self.fix_linux_principles_link(broken_links)
        
        print("\n" + "=" * 60)
        print(f"修复完成! 共修复 {self.fixed_count} 个链接")
        print("=" * 60)

if __name__ == '__main__':
    fixer = RemainingLinkFixer()
    fixer.run_all_fixes()
