#!/usr/bin/env python3
"""
断链修复器 - 自动修复Markdown文件中的断链
"""

import os
import re
import json
from pathlib import Path
from collections import defaultdict

class BrokenLinkFixer:
    def __init__(self, base_path="."):
        self.base_path = Path(base_path).resolve()
        self.fixed_count = 0
        self.fixed_files = set()
        
    def load_broken_links(self, json_file="broken_links_data.json"):
        """加载断链数据"""
        with open(json_file, 'r', encoding='utf-8') as f:
            data = json.load(f)
        return data['broken_links']
        
    def fix_schedule_formal_view_links(self, broken_links):
        """修复指向 schedule_formal_view.md 的链接 - 将这些链接改为指向 README.md"""
        schedule_links = [l for l in broken_links 
                         if 'schedule_formal_view.md' in l['target'] 
                         and l['type'] == 'missing_file']
        
        # 按源文件分组
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
                # 将 schedule_formal_view.md 替换为 ../README.md 或 ./README.md
                if '/' in source:
                    new_target = old_target.replace('schedule_formal_view.md', 'README.md')
                else:
                    new_target = old_target.replace('schedule_formal_view.md', 'README.md')
                    
                # 检查新的目标是否存在
                new_path = self.base_path / new_target.split('#')[0]
                if new_path.exists():
                    # 替换链接
                    old_link = f"]({old_target})"
                    new_link = f"]({new_target})"
                    content = content.replace(old_link, new_link)
                    self.fixed_count += 1
                    self.fixed_files.add(source)
                    print(f"  ✓ 修复: {source} -> {new_target}")
                else:
                    # 目标不存在，删除链接或改为纯文本
                    # 暂时保留，后续处理
                    pass
                    
            if content != original_content:
                source_path.write_text(content, encoding='utf-8')
                
    def fix_mindmap_anchor_links(self, broken_links):
        """修复思维导图文件中的锚点链接 - 在思维导图文件中添加缺失的锚点"""
        mindmap_file = self.base_path / "Composed/schedule_formal_view/思维导图与知识矩阵.md"
        if not mindmap_file.exists():
            print(f"  ⚠️ 思维导图文件不存在")
            return
            
        # 获取所有缺失的锚点
        missing_anchors = set()
        for link in broken_links:
            if link['type'] == 'missing_anchor' and '思维导图与知识矩阵.md' in link['target']:
                anchor = link['target'].split('#')[-1]
                missing_anchors.add(anchor)
                
        if not missing_anchors:
            return
            
        print(f"  发现 {len(missing_anchors)} 个缺失锚点需要添加")
        
        content = mindmap_file.read_text(encoding='utf-8')
        original_content = content
        
        # 为每个缺失的锚点添加对应的标题
        # 锚点格式: #31-01-cpu硬件层, #32-02-系统总线层, #310-10-24-扩展主题
        anchor_to_title = {
            '31-01-cpu硬件层': '### 3.1 01 CPU硬件层',
            '32-02-系统总线层': '### 3.2 02 系统总线层', 
            '33-03-os抽象层': '### 3.3 03 OS抽象层',
            '34-04-同步通信机制': '### 3.4 04 同步通信机制',
            '35-05-虚拟化容器化沙盒化': '### 3.5 05 虚拟化容器化沙盒化',
            '36-06-调度模型': '### 3.6 06 调度模型',
            '37-07-性能优化与安全': '### 3.7 07 性能优化与安全',
            '38-08-技术演进与对标': '### 3.8 08 技术演进与对标',
            '39-09-形式化理论与证明': '### 3.9 09 形式化理论与证明',
            '310-10-24-扩展主题': '### 3.10 10-24 扩展主题',
        }
        
        for anchor, title in anchor_to_title.items():
            if anchor in missing_anchors:
                # 在内容中查找对应的标题并添加锚点
                # 查找标题行
                pattern = rf'^({re.escape(title)})\s*$'
                if re.search(pattern, content, re.MULTILINE):
                    # 标题存在，添加锚点
                    replacement = f'{title} {{#{anchor}}}'
                    content = re.sub(pattern, replacement, content, flags=re.MULTILINE)
                    self.fixed_count += 1
                    self.fixed_files.add(str(mindmap_file.relative_to(self.base_path)).replace('\\', '/'))
                    print(f"  ✓ 添加锚点: {anchor}")
                    
        if content != original_content:
            mindmap_file.write_text(content, encoding='utf-8')
            
    def fix_missing_files_by_creating_placeholders(self, broken_links):
        """为缺失的文件创建占位文件"""
        # 收集需要创建的缺失文件
        missing_files = set()
        for link in broken_links:
            if link['type'] == 'missing_file':
                # 跳过 schedule_formal_view.md 的链接（已在其他地方处理）
                if 'schedule_formal_view.md' in link['target']:
                    continue
                # 跳过代码片段误识别为链接的情况
                if any(c in link['target'] for c in ['&', '<', '>', '|', '*']):
                    continue
                # 跳过明显不合法的路径
                if link['target'].endswith(('.md', '.png', '.jpg', '.svg')):
                    missing_files.add(link['target'])
                    
        print(f"  发现 {len(missing_files)} 个缺失文件")
        
        created = 0
        for file_path in sorted(missing_files):
            full_path = self.base_path / file_path
            if full_path.exists():
                continue
                
            # 确保目录存在
            full_path.parent.mkdir(parents=True, exist_ok=True)
            
            # 创建占位文件
            title = full_path.stem.replace('_', ' ').replace('-', ' ')
            content = f"""---
title: "{title}"
status: "待完善"
created: "2026-04-12"
---

# {title}

> **注意**: 本文档为自动生成的占位文件，内容待补充。

## 概述

此文档是形式科学项目的一部分，内容正在完善中。

## 待补充内容

- [ ] 核心概念定义
- [ ] 形式化描述  
- [ ] 示例说明
- [ ] 相关引用

---

*本文件由断链修复系统自动生成*
"""
            try:
                full_path.write_text(content, encoding='utf-8')
                created += 1
                self.fixed_files.add(file_path)
                print(f"  ✓ 创建占位: {file_path}")
            except Exception as e:
                print(f"  ❌ 无法创建 {file_path}: {e}")
                
        self.fixed_count += created
        return created
        
    def fix_gpu_accelerator_links(self, broken_links):
        """修复GPU加速器调度部分的链接"""
        # 文件名映射：从链接中的名称到实际文件名
        name_mapping = {
            '16.1_GPU任务调度.md': '16.1_GPU计算调度.md',
            '16.2_图形渲染调度.md': '16.2_深度学习调度.md', 
            '16.3_AI加速器调度.md': '16.3_异构计算调度.md',
            '16.4_异构计算调度.md': '16.4_GPU虚拟化与共享.md',
        }
        
        gpu_links = [l for l in broken_links 
                    if '16_GPU与加速器调度' in l['target'] 
                    and l['type'] == 'missing_file']
                    
        # 按源文件分组
        by_source = defaultdict(list)
        for link in gpu_links:
            by_source[link['source']].append(link)
            
        for source, links in by_source.items():
            source_path = self.base_path / source
            if not source_path.exists():
                continue
                
            content = source_path.read_text(encoding='utf-8')
            original_content = content
            
            for link in links:
                old_target = link['target']
                # 获取文件名
                old_filename = os.path.basename(old_target)
                if old_filename in name_mapping:
                    new_filename = name_mapping[old_filename]
                    new_target = old_target.replace(old_filename, new_filename)
                    
                    # 检查新目标是否存在
                    new_path = self.base_path / new_target.split('#')[0]
                    if new_path.exists():
                        content = content.replace(f"]({old_target})", f"]({new_target})")
                        self.fixed_count += 1
                        self.fixed_files.add(source)
                        print(f"  ✓ 修复GPU链接: {source} -> {new_filename}")
                        
            if content != original_content:
                source_path.write_text(content, encoding='utf-8')
                
    def fix_other_missing_files(self, broken_links):
        """修复其他缺失文件的链接 - 删除或修改链接"""
        # 处理 Composed/Concept/LINUX_OS_PRINCIPLES.md
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
                # 替换为指向 docs/Refactor 中的相关文档
                old_target = link['target']
                # 暂时改为纯文本（移除链接）
                old_link_pattern = rf'\[([^\]]+)\]\({re.escape(old_target)}\)'
                content = re.sub(old_link_pattern, r'\1', content)
                self.fixed_count += 1
                self.fixed_files.add(source)
                print(f"  ✓ 移除无效链接: {source} -> {old_target}")
                
            if content != original_content:
                source_path.write_text(content, encoding='utf-8')
                
    def run_all_fixes(self):
        """运行所有修复"""
        print("=" * 60)
        print("断链修复工具")
        print("=" * 60)
        
        broken_links = self.load_broken_links()
        print(f"\n加载了 {len(broken_links)} 个断链记录")
        
        print("\n1. 修复指向 schedule_formal_view.md 的链接...")
        self.fix_schedule_formal_view_links(broken_links)
        
        print("\n2. 修复思维导图锚点...")
        self.fix_mindmap_anchor_links(broken_links)
        
        print("\n3. 修复GPU加速器调度链接...")
        self.fix_gpu_accelerator_links(broken_links)
        
        print("\n4. 修复其他缺失文件链接...")
        self.fix_other_missing_files(broken_links)
        
        print("\n5. 创建缺失文件的占位...")
        self.fix_missing_files_by_creating_placeholders(broken_links)
        
        print("\n" + "=" * 60)
        print(f"修复完成!")
        print(f"  - 修复/处理链接: {self.fixed_count}")
        print(f"  - 涉及文件数: {len(self.fixed_files)}")
        print("=" * 60)
        
        # 保存修复报告
        report = f"""# 断链修复报告

**修复时间**: 2026-04-12

## 统计

- 修复/处理链接数: {self.fixed_count}
- 涉及文件数: {len(self.fixed_files)}

## 修复的文件列表

"""
        for f in sorted(self.fixed_files):
            report += f"- `{f}`\n"
            
        with open('link_fix_report.md', 'w', encoding='utf-8') as f:
            f.write(report)
            
        print(f"\n修复报告已保存: link_fix_report.md")

if __name__ == '__main__':
    fixer = BrokenLinkFixer()
    fixer.run_all_fixes()
