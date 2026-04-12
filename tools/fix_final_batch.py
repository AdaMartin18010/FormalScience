#!/usr/bin/env python3
"""
最终批量修复
"""

import os
import re
import json
from pathlib import Path
from collections import defaultdict

class FinalBatchFixer:
    def __init__(self, base_path="."):
        self.base_path = Path(base_path).resolve()
        self.fixed_count = 0
        
    def load_broken_links(self, json_file="broken_links_data.json"):
        with open(json_file, 'r', encoding='utf-8') as f:
            data = json.load(f)
        return data['broken_links']
        
    def fix_linux_principles_link(self, broken_links):
        """修复 LINUX_OS_PRINCIPLES.md 链接 - 改为纯文本"""
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
                print(f"  ✓ 转换链接为文本: {source}")
                
            if content != original_content:
                source_path.write_text(content, encoding='utf-8')
                
    def fix_code_snippet_links(self, broken_links):
        """修复代码片段误识别为链接的问题"""
        # 这些是被误识别的链接
        invalid_patterns = [
            (r'\[s\]\(Composed/schedule_formal_view/11_企业架构调度/k\)', 's'),
            (r'\[&\]\(Composed/schedule_formal_view/16_GPU与加速器调度/handler& h\)', '&'),
            (r'\[=\]\(Composed/schedule_formal_view/16_GPU与加速器调度/id<1> i\)', '='),
        ]
        
        for source_file, links in defaultdict(list).items():
            pass
            
        # 直接修复特定文件
        files_to_fix = [
            "Composed/schedule_formal_view/11_企业架构调度/11.3_应用架构层调度.md",
            "Composed/schedule_formal_view/16_GPU与加速器调度/16.3_异构计算调度.md",
        ]
        
        for file_path in files_to_fix:
            full_path = self.base_path / file_path
            if not full_path.exists():
                continue
                
            content = full_path.read_text(encoding='utf-8')
            original_content = content
            
            # 修复 [s](k) 模式
            content = re.sub(r'\[s\]\(k\)', '`s`', content)
            # 修复 [&](handler& h) 模式
            content = re.sub(r'\[&\]\(handler& h\)', '`&`', content)
            # 修复 [=](id<1> i) 模式
            content = re.sub(r'\[=\]\(id<1> i\)', '`=`', content)
            
            if content != original_content:
                full_path.write_text(content, encoding='utf-8')
                self.fixed_count += 1
                print(f"  ✓ 修复代码片段链接: {file_path}")
                
    def fix_mindmap_links_by_removing_anchor(self, broken_links):
        """修复思维导图链接 - 移除锚点只保留文件链接"""
        mindmap_links = [l for l in broken_links 
                        if '思维导图与知识矩阵.md' in l['target'] 
                        and l['type'] == 'missing_anchor']
        
        by_source = defaultdict(list)
        for link in mindmap_links:
            by_source[link['source']].append(link)
            
        for source, links in by_source.items():
            source_path = self.base_path / source
            if not source_path.exists():
                continue
                
            content = source_path.read_text(encoding='utf-8')
            original_content = content
            
            for link in links:
                old_target = link['target']  # 如: 思维导图与知识矩阵.md#31-01-cpu硬件层
                # 只保留文件部分，移除锚点
                new_target = old_target.split('#')[0]
                
                old_pattern = re.escape(f"]({old_target})")
                content = re.sub(old_pattern, f"]({new_target})", content)
                self.fixed_count += 1
                print(f"  ✓ 移除锚点: {source} -> {new_target}")
                
            if content != original_content:
                source_path.write_text(content, encoding='utf-8')
                
    def fix_schedule_anchors_by_removing(self, broken_links):
        """修复 schedule_formal_view.md 的锚点链接 - 移除锚点"""
        schedule_links = [l for l in broken_links 
                         if 'schedule_formal_view.md' in l['target'] 
                         and l['type'] == 'missing_anchor']
        
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
                # 只保留文件部分
                new_target = "README.md"
                
                old_pattern = re.escape(f"]({old_target})")
                content = re.sub(old_pattern, f"]({new_target})", content)
                self.fixed_count += 1
                print(f"  ✓ 更改链接: {source} -> {new_target}")
                
            if content != original_content:
                source_path.write_text(content, encoding='utf-8')
                
    def run_all_fixes(self):
        """运行所有修复"""
        print("=" * 60)
        print("最终批量修复")
        print("=" * 60)
        
        broken_links = self.load_broken_links()
        print(f"\n加载了 {len(broken_links)} 个断链记录")
        
        print("\n1. 修复代码片段误识别链接...")
        self.fix_code_snippet_links(broken_links)
        
        print("\n2. 修复 LINUX_OS_PRINCIPLES.md 链接...")
        self.fix_linux_principles_link(broken_links)
        
        print("\n3. 修复思维导图锚点链接...")
        self.fix_mindmap_links_by_removing_anchor(broken_links)
        
        print("\n4. 修复 schedule_formal_view.md 锚点链接...")
        self.fix_schedule_anchors_by_removing(broken_links)
        
        print("\n" + "=" * 60)
        print(f"修复完成! 共修复 {self.fixed_count} 个问题")
        print("=" * 60)

if __name__ == '__main__':
    fixer = FinalBatchFixer()
    fixer.run_all_fixes()
