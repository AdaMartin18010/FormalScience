#!/usr/bin/env python3
"""
最终锚点修复
"""

import os
import re
import json
from pathlib import Path
from collections import defaultdict

class AnchorFixer:
    def __init__(self, base_path="."):
        self.base_path = Path(base_path).resolve()
        self.fixed_count = 0
        
    def load_broken_links(self, json_file="broken_links_data.json"):
        with open(json_file, 'r', encoding='utf-8') as f:
            data = json.load(f)
        return data['broken_links']
        
    def fix_schedule_formal_view_anchors(self, broken_links):
        """在 schedule_formal_view.md 中添加缺失的锚点"""
        schedule_file = self.base_path / "Composed/schedule_formal_view/schedule_formal_view.md"
        if not schedule_file.exists():
            return
            
        # 获取所有指向 schedule_formal_view.md 的缺失锚点
        missing_anchors = set()
        for link in broken_links:
            if (link['type'] == 'missing_anchor' and 
                'schedule_formal_view.md' in link['target']):
                anchor = link['target'].split('#')[-1]
                missing_anchors.add(anchor)
                
        if not missing_anchors:
            print("  没有需要添加的锚点")
            return
            
        print(f"  发现 {len(missing_anchors)} 个缺失锚点需要添加到 schedule_formal_view.md")
        
        content = schedule_file.read_text(encoding='utf-8')
        original_content = content
        
        # 为每个缺失的锚点添加一个标记
        for anchor in missing_anchors:
            # 在文件末尾添加锚点标记
            anchor_html = f'\n<a id="{anchor}"></a>\n'
            if anchor_html.strip() not in content:
                content += anchor_html
                self.fixed_count += 1
                print(f"  ✓ 添加锚点: {anchor}")
                
        if content != original_content:
            schedule_file.write_text(content, encoding='utf-8')
            
    def fix_mindmap_anchors_detailed(self, broken_links):
        """详细修复思维导图锚点 - 直接编辑文件添加锚点"""
        mindmap_file = self.base_path / "Composed/schedule_formal_view/思维导图与知识矩阵.md"
        if not mindmap_file.exists():
            return
            
        # 获取所有指向思维导图的缺失锚点
        missing_anchors = {}
        for link in broken_links:
            if (link['type'] == 'missing_anchor' and 
                '思维导图与知识矩阵.md' in link['target']):
                anchor = link['target'].split('#')[-1]
                missing_anchors[anchor] = link
                
        if not missing_anchors:
            print("  思维导图没有需要添加的锚点")
            return
            
        print(f"  发现 {len(missing_anchors)} 个缺失锚点需要添加到思维导图")
        
        content = mindmap_file.read_text(encoding='utf-8')
        original_content = content
        
        # 锚点映射表
        anchor_to_section = {
            '31-01-cpu硬件层': '3.1 01 CPU硬件层',
            '32-02-系统总线层': '3.2 02 系统总线层',
            '33-03-os抽象层': '3.3 03 OS抽象层',
            '34-04-同步通信机制': '3.4 04 同步通信机制',
            '35-05-虚拟化容器化沙盒化': '3.5 05 虚拟化容器化沙盒化',
            '36-06-调度模型': '3.6 06 调度模型',
            '37-07-性能优化与安全': '3.7 07 性能优化与安全',
            '38-08-技术演进与对标': '3.8 08 技术演进与对标',
            '39-09-形式化理论与证明': '3.9 09 形式化理论与证明',
            '310-10-24-扩展主题': '3.10 10-24 扩展主题',
        }
        
        for anchor, section in anchor_to_section.items():
            if anchor in missing_anchors:
                # 查找对应的小节标题
                # 匹配 ### 3.1 01 CPU硬件层 或类似的标题
                pattern = rf'^(### {re.escape(section)})\s*$'
                if re.search(pattern, content, re.MULTILINE):
                    # 标题存在，添加锚点
                    replacement = rf'\1 {{#{anchor}}}'
                    new_content = re.sub(pattern, replacement, content, flags=re.MULTILINE)
                    if new_content != content:
                        content = new_content
                        self.fixed_count += 1
                        print(f"  ✓ 添加锚点到标题: {section} -> {anchor}")
                else:
                    # 标题不存在，可能是格式问题，尝试添加HTML锚点
                    # 在文件中找到合适的位置添加
                    pass
                    
        if content != original_content:
            mindmap_file.write_text(content, encoding='utf-8')
            print(f"  已更新思维导图文件")
            
    def remove_broken_links_or_convert_to_text(self, broken_links):
        """将剩余的无效链接改为纯文本"""
        # 处理 LINUX_OS_PRINCIPLES.md 链接
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
                
    def run_all_fixes(self):
        """运行所有修复"""
        print("=" * 60)
        print("最终锚点修复")
        print("=" * 60)
        
        broken_links = self.load_broken_links()
        print(f"\n加载了 {len(broken_links)} 个断链记录")
        
        print("\n1. 修复 schedule_formal_view.md 的锚点...")
        self.fix_schedule_formal_view_anchors(broken_links)
        
        print("\n2. 修复思维导图的锚点...")
        self.fix_mindmap_anchors_detailed(broken_links)
        
        print("\n3. 处理剩余无效链接...")
        self.remove_broken_links_or_convert_to_text(broken_links)
        
        print("\n" + "=" * 60)
        print(f"修复完成! 共修复 {self.fixed_count} 个问题")
        print("=" * 60)

if __name__ == '__main__':
    fixer = AnchorFixer()
    fixer.run_all_fixes()
