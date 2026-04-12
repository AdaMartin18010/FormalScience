#!/usr/bin/env python3
"""
断链扫描器 - 扫描Markdown文件中的断链
"""

import os
import re
import json
from pathlib import Path
from collections import defaultdict

# 目标目录列表
TARGET_DIRS = [
    "docs/Refactor/01_数学基础",
    "docs/Refactor/02_形式语言", 
    "docs/Refactor/03_编程范式",
    "docs/Refactor/04_软件工程",
    "docs/Refactor/05_形式化理论",
    "docs/Refactor/06_调度系统",
    "Composed/schedule_formal_view",
]

class BrokenLinkScanner:
    def __init__(self, base_path="."):
        self.base_path = Path(base_path).resolve()
        self.broken_links = []
        self.all_files = set()
        self.file_anchors = defaultdict(set)
        
    def collect_all_files(self):
        """收集所有目标目录中的文件"""
        print("正在收集文件列表...")
        for target_dir in TARGET_DIRS:
            full_path = self.base_path / target_dir
            if not full_path.exists():
                print(f"  ⚠️ 目录不存在: {target_dir}")
                continue
            for ext in ['.md', '.png', '.jpg', '.jpeg', '.gif', '.svg', '.pdf']:
                for f in full_path.rglob(f"*{ext}"):
                    rel_path = f.relative_to(self.base_path)
                    self.all_files.add(str(rel_path).replace('\\', '/'))
        print(f"  找到 {len(self.all_files)} 个文件")
        
    def extract_anchors(self, content, file_path):
        """提取文件中的所有锚点"""
        anchors = set()
        # 标题锚点
        for match in re.finditer(r'^#{1,6}\s+(.+)$', content, re.MULTILINE):
            title = match.group(1).strip()
            # GitHub风格的锚点生成
            anchor = re.sub(r'[^\w\s-]', '', title).lower().strip()
            anchor = re.sub(r'[-\s]+', '-', anchor)
            anchors.add(anchor)
        # HTML锚点
        for match in re.finditer(r'<a[^>]+name=["\']([^"\']+)["\']', content):
            anchors.add(match.group(1))
        for match in re.finditer(r'<a[^>]+id=["\']([^"\']+)["\']', content):
            anchors.add(match.group(1))
        return anchors
        
    def scan_file(self, file_path):
        """扫描单个文件中的链接"""
        try:
            content = file_path.read_text(encoding='utf-8')
        except Exception as e:
            print(f"  ❌ 无法读取文件: {file_path} - {e}")
            return
            
        rel_path = str(file_path.relative_to(self.base_path)).replace('\\', '/')
        file_dir = os.path.dirname(rel_path)
        
        # 提取锚点
        anchors = self.extract_anchors(content, file_path)
        self.file_anchors[rel_path] = anchors
        
        # 查找所有Markdown链接 [text](url)
        for match in re.finditer(r'!?\[([^\]]*)\]\(([^)]+)\)', content):
            link_text = match.group(1)
            link_url = match.group(2).strip()
            
            # 跳过外部链接
            if link_url.startswith(('http://', 'https://', 'mailto:', 'tel:', '#')):
                continue
                
            # 处理锚点
            anchor = None
            if '#' in link_url:
                parts = link_url.split('#', 1)
                link_url = parts[0]
                anchor = parts[1]
                
            # 空链接表示当前文件的锚点
            if not link_url:
                if anchor and anchor not in anchors:
                    self.broken_links.append({
                        'source': rel_path,
                        'link_text': link_text,
                        'target': f"#{anchor}",
                        'type': 'missing_anchor',
                        'line': content[:match.start()].count('\n') + 1
                    })
                continue
                
            # 解析相对路径
            if link_url.startswith('/'):
                target_path = link_url[1:]
            else:
                target_path = os.path.normpath(os.path.join(file_dir, link_url)).replace('\\', '/')
                
            # 检查文件是否存在
            if target_path not in self.all_files:
                self.broken_links.append({
                    'source': rel_path,
                    'link_text': link_text,
                    'target': target_path,
                    'anchor': anchor,
                    'type': 'missing_file',
                    'line': content[:match.start()].count('\n') + 1
                })
            elif anchor:
                # 文件存在，检查锚点（延迟检查，需要读取目标文件）
                self.broken_links.append({
                    'source': rel_path,
                    'link_text': link_text,
                    'target': target_path,
                    'anchor': anchor,
                    'type': 'anchor_check_pending',
                    'line': content[:match.start()].count('\n') + 1
                })
                
    def check_anchors(self):
        """检查待验证的锚点"""
        print("正在验证锚点...")
        pending = [l for l in self.broken_links if l['type'] == 'anchor_check_pending']
        
        # 加载目标文件的锚点
        target_files = set(l['target'] for l in pending)
        for target_file in target_files:
            full_path = self.base_path / target_file
            if full_path.exists():
                try:
                    content = full_path.read_text(encoding='utf-8')
                    self.file_anchors[target_file] = self.extract_anchors(content, full_path)
                except:
                    pass
                    
        # 验证锚点
        for link in pending:
            target = link['target']
            anchor = link['anchor']
            if anchor not in self.file_anchors.get(target, set()):
                link['type'] = 'missing_anchor'
            else:
                link['type'] = 'valid'
                
        # 过滤掉有效的链接
        self.broken_links = [l for l in self.broken_links if l['type'] != 'valid']
        
    def scan_all(self):
        """扫描所有目标目录"""
        self.collect_all_files()
        
        print("\n正在扫描Markdown文件...")
        md_files = []
        for target_dir in TARGET_DIRS:
            full_path = self.base_path / target_dir
            if full_path.exists():
                md_files.extend(full_path.rglob("*.md"))
                
        for i, md_file in enumerate(md_files, 1):
            if i % 50 == 0:
                print(f"  已扫描 {i}/{len(md_files)} 个文件...")
            self.scan_file(md_file)
            
        self.check_anchors()
        
    def generate_report(self):
        """生成报告"""
        report_lines = []
        report_lines.append("# 断链扫描报告")
        report_lines.append("")
        report_lines.append(f"**扫描时间**: 2026-04-12")
        report_lines.append(f"**扫描目录**: {len(TARGET_DIRS)} 个核心模块")
        report_lines.append(f"**发现断链**: {len(self.broken_links)} 个")
        report_lines.append("")
        
        # 按类型统计
        type_counts = defaultdict(int)
        for link in self.broken_links:
            type_counts[link['type']] += 1
            
        report_lines.append("## 统计摘要")
        report_lines.append("")
        report_lines.append("| 类型 | 数量 |")
        report_lines.append("|------|------|")
        report_lines.append(f"| 缺失文件 | {type_counts.get('missing_file', 0)} |")
        report_lines.append(f"| 缺失锚点 | {type_counts.get('missing_anchor', 0)} |")
        report_lines.append("")
        
        # 按源文件分组
        by_source = defaultdict(list)
        for link in self.broken_links:
            by_source[link['source']].append(link)
            
        report_lines.append("## 断链详情")
        report_lines.append("")
        
        for source, links in sorted(by_source.items()):
            report_lines.append(f"### {source}")
            report_lines.append("")
            report_lines.append("| 行号 | 链接文本 | 目标 | 问题类型 |")
            report_lines.append("|------|----------|------|----------|")
            for link in links:
                target = link['target']
                if link.get('anchor'):
                    target += f"#{link['anchor']}"
                type_name = "缺失文件" if link['type'] == 'missing_file' else "缺失锚点"
                report_lines.append(f"| {link['line']} | {link['link_text']} | `{target}` | {type_name} |")
            report_lines.append("")
            
        # 生成修复建议
        report_lines.append("## 修复建议")
        report_lines.append("")
        
        # 收集需要创建的文件
        missing_files = set()
        for link in self.broken_links:
            if link['type'] == 'missing_file':
                missing_files.add(link['target'])
                
        if missing_files:
            report_lines.append(f"### 需要创建的文件 ({len(missing_files)}个)")
            report_lines.append("")
            for f in sorted(missing_files)[:50]:  # 最多显示50个
                report_lines.append(f"- `{f}`")
            if len(missing_files) > 50:
                report_lines.append(f"- ... 还有 {len(missing_files) - 50} 个")
            report_lines.append("")
            
        return '\n'.join(report_lines)
        
    def save_json(self, output_file):
        """保存JSON格式的详细数据"""
        data = {
            'broken_links': self.broken_links,
            'stats': {
                'total': len(self.broken_links),
                'missing_file': len([l for l in self.broken_links if l['type'] == 'missing_file']),
                'missing_anchor': len([l for l in self.broken_links if l['type'] == 'missing_anchor']),
            }
        }
        with open(output_file, 'w', encoding='utf-8') as f:
            json.dump(data, f, ensure_ascii=False, indent=2)

if __name__ == '__main__':
    scanner = BrokenLinkScanner()
    scanner.scan_all()
    
    # 保存报告
    report = scanner.generate_report()
    with open('broken_links_report.md', 'w', encoding='utf-8') as f:
        f.write(report)
    
    # 保存JSON数据
    scanner.save_json('broken_links_data.json')
    
    print(f"\n✅ 扫描完成!")
    print(f"   发现断链: {len(scanner.broken_links)} 个")
    print(f"   报告已保存: broken_links_report.md")
    print(f"   数据已保存: broken_links_data.json")
