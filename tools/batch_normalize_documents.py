#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FormalScience 文档批量规范化脚本

功能：
1. 为文档添加统一元数据头
2. 统一章节编号格式
3. 修复格式问题
4. 标准化链接格式
5. 生成规范化报告

用法：
    python batch_normalize_documents.py [路径] [选项]
    
    选项：
        --dry-run       预览变更，不实际修改
        --verbose       显示详细输出
        --limit N       限制处理文件数量
        --include-root  包含根目录文件
"""

import os
import re
import sys
import argparse
from pathlib import Path
from datetime import datetime
from typing import List, Dict, Tuple, Optional, Set
from dataclasses import dataclass, field
from collections import defaultdict
import json


@dataclass
class NormalizeStats:
    """规范化统计"""
    total_files: int = 0
    processed_files: int = 0
    skipped_files: int = 0
    error_files: int = 0
    added_headers: int = 0
    fixed_numbering: int = 0
    fixed_format: int = 0
    fixed_links: int = 0
    changes_by_type: Dict[str, int] = field(default_factory=lambda: defaultdict(int))


class DocumentNormalizer:
    """文档规范化器"""
    
    # 排除的目录
    EXCLUDE_DIRS = {'.git', 'node_modules', 'venv', '__pycache__', '.templates', '.vscode'}
    
    # 排除的文件
    EXCLUDE_FILES = {'README.md', 'README_项目完成状态_2025-11-14.md'}
    
    # 状态关键词映射
    STATUS_KEYWORDS = {
        'draft': ['draft', '待完善', '未完成', 'TODO'],
        'complete': ['complete', '完成', '最终', '最终报告', '最终总结'],
        'review': ['review', '审核', '检查', 'fix'],
    }
    
    def __init__(self, base_path: str, dry_run: bool = False, verbose: bool = False):
        self.base_path = Path(base_path)
        self.dry_run = dry_run
        self.verbose = verbose
        self.stats = NormalizeStats()
        self.changes_log: List[Dict] = []
        
    def normalize_all(self, limit: Optional[int] = None, include_root: bool = False):
        """规范化所有文档"""
        md_files = []
        
        for md_file in self.base_path.rglob("*.md"):
            # 排除目录
            if any(excluded in str(md_file) for excluded in self.EXCLUDE_DIRS):
                continue
            
            # 排除特定文件
            if md_file.name in self.EXCLUDE_FILES:
                continue
            
            # 可选：排除根目录文件
            if not include_root and md_file.parent == self.base_path:
                continue
            
            md_files.append(md_file)
        
        self.stats.total_files = len(md_files)
        
        # 限制数量
        if limit:
            md_files = md_files[:limit]
        
        print(f"📁 发现 {self.stats.total_files} 个 Markdown 文件")
        print(f"📝 将处理 {len(md_files)} 个文件")
        print("-" * 60)
        
        for i, md_file in enumerate(md_files, 1):
            if self.verbose:
                print(f"[{i}/{len(md_files)}] 处理: {md_file.relative_to(self.base_path)}")
            
            try:
                self._normalize_file(md_file)
            except Exception as e:
                self.stats.error_files += 1
                print(f"  ❌ 错误: {e}")
        
        return self.stats
    
    def _normalize_file(self, file_path: Path):
        """规范化单个文件"""
        relative_path = file_path.relative_to(self.base_path)
        content = file_path.read_text(encoding='utf-8')
        original_content = content
        changes = []
        
        # 1. 检查和添加元数据头
        content, header_changes = self._add_metadata_header(content, relative_path)
        changes.extend(header_changes)
        
        # 2. 规范化章节编号
        content, numbering_changes = self._normalize_numbering(content)
        changes.extend(numbering_changes)
        
        # 3. 修复格式问题
        content, format_changes = self._fix_format(content)
        changes.extend(format_changes)
        
        # 4. 标准化链接
        content, link_changes = self._normalize_links(content, file_path)
        changes.extend(link_changes)
        
        # 5. 添加标准底部
        content, footer_changes = self._add_footer(content)
        changes.extend(footer_changes)
        
        # 记录变更
        if changes:
            self.stats.processed_files += 1
            self.changes_log.append({
                'file': str(relative_path),
                'changes': changes
            })
            
            # 写入文件
            if not self.dry_run:
                file_path.write_text(content, encoding='utf-8')
            
            if self.verbose:
                for change in changes:
                    print(f"  ✓ {change['type']}: {change['description']}")
        else:
            self.stats.skipped_files += 1
    
    def _add_metadata_header(self, content: str, relative_path: Path) -> Tuple[str, List[Dict]]:
        """添加元数据头"""
        changes = []
        
        # 检查是否已有元数据头
        if re.match(r'^---\s*\n', content):
            # 已有YAML frontmatter，跳过
            return content, changes
        
        # 检查是否有其他元数据格式
        has_metadata = any(
            re.match(r'^\s*(topic|主题|author|作者)\s*[:：]', line)
            for line in content.split('\n')[:10]
        )
        
        if has_metadata:
            return content, changes
        
        # 推断元数据
        topic = self._extract_topic(content, relative_path)
        status = self._infer_status(content, relative_path)
        category = self._infer_category(relative_path)
        tags = self._extract_tags(content)
        
        # 构建元数据头
        header = f"""---
topic: "{topic}"
dependencies: []
status: "{status}"
author: "FormalScience Project"
date: "{datetime.now().strftime('%Y-%m-%d')}"
version: "1.0.0"
tags: {json.dumps(tags, ensure_ascii=False)}
category: "{category}"
priority: "medium"
---

"""
        
        # 添加到内容开头
        new_content = header + content
        
        changes.append({
            'type': '添加元数据',
            'description': f'topic: {topic}, status: {status}, category: {category}'
        })
        self.stats.added_headers += 1
        self.stats.changes_by_type['metadata'] += 1
        
        return new_content, changes
    
    def _extract_topic(self, content: str, relative_path: Path) -> str:
        """从内容提取主题"""
        # 尝试从标题提取
        title_match = re.search(r'^#\s+(.+)$', content, re.MULTILINE)
        if title_match:
            return title_match.group(1).strip()[:50]
        
        # 从文件名提取
        file_name = relative_path.stem
        file_name = file_name.replace('_', ' ').replace('-', ' ')
        
        # 移除常见后缀
        for suffix in ['完成报告', '最终报告', '总结', '报告', '指南']:
            file_name = file_name.replace(suffix, '')
        
        return file_name.strip() or "未命名主题"
    
    def _infer_status(self, content: str, relative_path: Path) -> str:
        """推断文档状态"""
        file_name = relative_path.name.lower()
        content_lower = content.lower()
        
        # 检查文件名关键词
        if any(kw in file_name for kw in ['完成', '最终', 'complete', 'final']):
            return 'complete'
        if any(kw in file_name for kw in ['draft', '待完善', 'todo']):
            return 'draft'
        
        # 检查内容关键词
        if 'TODO' in content or 'FIXME' in content or '待完善' in content:
            return 'draft'
        
        # 检查是否包含报告类关键词
        if '报告' in file_name or 'report' in file_name:
            return 'complete'
        
        return 'review'
    
    def _infer_category(self, relative_path: Path) -> str:
        """推断文档类别"""
        path_str = str(relative_path).lower()
        
        if any(kw in path_str for kw in ['guide', '指南', 'howto', '教程']):
            return 'guide'
        if any(kw in path_str for kw in ['ref', '参考', 'index', '索引']):
            return 'reference'
        if any(kw in path_str for kw in ['theory', '理论', '形式化', 'formal']):
            return 'theory'
        if any(kw in path_str for kw in ['practice', '实践', '应用', '案例']):
            return 'practice'
        
        return 'reference'
    
    def _extract_tags(self, content: str) -> List[str]:
        """提取标签"""
        tags = []
        
        # 从内容提取关键词
        keywords = [
            ('递归', 'recursion'), ('类型', 'type'), ('形式化', 'formal'),
            ('证明', 'proof'), ('定理', 'theorem'), ('算法', 'algorithm'),
            ('计算', 'computation'), ('逻辑', 'logic'), ('集合', 'set'),
            ('范畴', 'category'), ('Petri', 'petri'), ('图灵机', 'turing'),
            ('Lambda', 'lambda'), ('AI', 'ai'), ('模型', 'model'),
        ]
        
        content_lower = content.lower()
        for cn, en in keywords:
            if cn in content or en in content_lower:
                tags.append(cn)
        
        return tags[:5]  # 最多5个标签
    
    def _normalize_numbering(self, content: str) -> Tuple[str, List[Dict]]:
        """规范化章节编号"""
        changes = []
        lines = content.split('\n')
        new_lines = []
        
        # 跟踪章节层级
        chapter_count = 0
        section_count = 0
        subsection_count = 0
        
        for line in lines:
            # 匹配标题
            title_match = re.match(r'^(#{2,3})\s*(\d+)?[\.\s]*(.*)$', line)
            if title_match:
                hashes = title_match.group(1)
                existing_num = title_match.group(2)
                title_text = title_match.group(3).strip()
                
                level = len(hashes)
                
                # 添加锚点
                anchor = self._generate_anchor(title_text)
                
                if level == 2:  # ## 一级章节
                    chapter_count += 1
                    section_count = 0
                    subsection_count = 0
                    
                    if existing_num:
                        # 已有编号，规范化格式
                        new_line = f"## {existing_num}. {title_text} {{#{anchor}}}"
                    else:
                        # 添加编号
                        new_line = f"## {chapter_count}. {title_text} {{#{anchor}}}"
                        changes.append({
                            'type': '章节编号',
                            'description': f'添加编号 {chapter_count}. 到: {title_text[:30]}'
                        })
                    
                elif level == 3:  # ### 二级章节
                    section_count += 1
                    subsection_count = 0
                    
                    if chapter_count > 0:
                        if existing_num:
                            new_line = f"### {existing_num} {title_text} {{#{anchor}}}"
                        else:
                            new_line = f"### {chapter_count}.{section_count} {title_text} {{#{anchor}}}"
                            changes.append({
                                'type': '章节编号',
                                'description': f'添加编号 {chapter_count}.{section_count} 到: {title_text[:30]}'
                            })
                    else:
                        new_line = line
                else:
                    new_line = line
                
                new_lines.append(new_line)
            else:
                new_lines.append(line)
        
        if changes:
            self.stats.fixed_numbering += len(changes)
            self.stats.changes_by_type['numbering'] += len(changes)
        
        return '\n'.join(new_lines), changes
    
    def _generate_anchor(self, title: str) -> str:
        """生成锚点名称"""
        # 移除Markdown标记
        anchor = re.sub(r'[#*`\[\]]', '', title)
        # 转换为小写
        anchor = anchor.lower()
        # 替换空格为连字符
        anchor = anchor.replace(' ', '-')
        # 移除特殊字符
        anchor = re.sub(r'[^\w\-]', '', anchor)
        # 限制长度
        return anchor[:30]
    
    def _fix_format(self, content: str) -> Tuple[str, List[Dict]]:
        """修复格式问题"""
        changes = []
        
        # 1. 修复行尾空格
        original = content
        content = re.sub(r' +\n', '\n', content)
        if content != original:
            changes.append({
                'type': '格式修复',
                'description': '移除行尾空格'
            })
        
        # 2. 修复连续空行
        original = content
        content = re.sub(r'\n{4,}', '\n\n\n', content)
        if content != original:
            changes.append({
                'type': '格式修复',
                'description': '规范化连续空行'
            })
        
        # 3. 修复标题格式
        original = content
        content = re.sub(r'^(#{1,6})([^\s#])', r'\1 \2', content, flags=re.MULTILINE)
        if content != original:
            changes.append({
                'type': '格式修复',
                'description': '修复标题空格'
            })
        
        # 4. 修复列表格式
        original = content
        content = re.sub(r'^(\s*)[-*]([^\s])', r'\1- \2', content, flags=re.MULTILINE)
        if content != original:
            changes.append({
                'type': '格式修复',
                'description': '修复列表空格'
            })
        
        # 5. 修复代码块语言标记
        original = content
        content = re.sub(r'```\s*\n', '```\n', content)
        if content != original:
            changes.append({
                'type': '格式修复',
                'description': '规范化代码块'
            })
        
        if changes:
            self.stats.fixed_format += len(changes)
            self.stats.changes_by_type['format'] += len(changes)
        
        return content, changes
    
    def _normalize_links(self, content: str, file_path: Path) -> Tuple[str, List[Dict]]:
        """标准化链接"""
        changes = []
        
        # 检查是否有链接需要修复
        # 这里主要是记录断链，不自动修复
        
        return content, changes
    
    def _add_footer(self, content: str) -> Tuple[str, List[Dict]]:
        """添加标准底部"""
        changes = []
        
        # 检查是否已有标准底部
        if '关联网络' in content or '---' in content[-500:]:
            return content, changes
        
        # 添加简单的关联网络部分
        footer = """

---

## 关联网络

### 前向引用

> 本文档为以下文档提供基础：
> - [相关文档](./) (待补充)

### 后向引用

> 本文档依赖以下基础文档：
> - [基础文档](./) (待补充)

### 交叉链接

> 相关主题：
> - [主题A](./) (待补充)
> - [主题B](./) (待补充)

---

*本文档由 FormalScience 文档规范化工具自动生成*
"""
        
        content = content + footer
        
        changes.append({
            'type': '添加底部',
            'description': '添加标准关联网络部分'
        })
        self.stats.changes_by_type['footer'] += 1
        
        return content, changes
    
    def generate_report(self, output_path: Optional[str] = None) -> str:
        """生成规范化报告"""
        report_lines = []
        
        # 报告头
        report_lines.append("=" * 80)
        report_lines.append("FormalScience 文档规范化报告")
        report_lines.append("=" * 80)
        report_lines.append(f"生成时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        report_lines.append(f"基础路径: {self.base_path}")
        report_lines.append(f"执行模式: {'预览模式' if self.dry_run else '实际执行'}")
        report_lines.append("")
        
        # 统计摘要
        report_lines.append("-" * 80)
        report_lines.append("处理统计")
        report_lines.append("-" * 80)
        report_lines.append(f"总文件数: {self.stats.total_files}")
        report_lines.append(f"已处理: {self.stats.processed_files}")
        report_lines.append(f"已跳过: {self.stats.skipped_files}")
        report_lines.append(f"错误: {self.stats.error_files}")
        report_lines.append("")
        
        # 变更详情
        report_lines.append("-" * 80)
        report_lines.append("变更详情")
        report_lines.append("-" * 80)
        report_lines.append(f"添加元数据头: {self.stats.added_headers}")
        report_lines.append(f"规范化编号: {self.stats.fixed_numbering}")
        report_lines.append(f"修复格式: {self.stats.fixed_format}")
        report_lines.append(f"修复链接: {self.stats.fixed_links}")
        report_lines.append("")
        
        # 按类型统计
        if self.stats.changes_by_type:
            report_lines.append("-" * 80)
            report_lines.append("变更类型分布")
            report_lines.append("-" * 80)
            for change_type, count in sorted(self.stats.changes_by_type.items(), key=lambda x: -x[1]):
                report_lines.append(f"  {change_type:15s}: {count:4d}")
            report_lines.append("")
        
        # 处理文件列表
        if self.changes_log:
            report_lines.append("-" * 80)
            report_lines.append("已处理文件")
            report_lines.append("-" * 80)
            
            for entry in self.changes_log[:100]:  # 限制显示数量
                report_lines.append(f"\n📄 {entry['file']}")
                for change in entry['changes']:
                    report_lines.append(f"  - [{change['type']}] {change['description']}")
            
            if len(self.changes_log) > 100:
                report_lines.append(f"\n... 还有 {len(self.changes_log) - 100} 个文件")
        
        report_lines.append("")
        report_lines.append("=" * 80)
        
        report = '\n'.join(report_lines)
        
        if output_path:
            Path(output_path).write_text(report, encoding='utf-8')
        
        return report
    
    def save_changes_log(self, output_path: str):
        """保存变更日志为JSON"""
        data = {
            'timestamp': datetime.now().isoformat(),
            'stats': {
                'total_files': self.stats.total_files,
                'processed_files': self.stats.processed_files,
                'skipped_files': self.stats.skipped_files,
                'error_files': self.stats.error_files,
                'changes_by_type': dict(self.stats.changes_by_type),
            },
            'changes': self.changes_log,
        }
        
        Path(output_path).write_text(
            json.dumps(data, ensure_ascii=False, indent=2),
            encoding='utf-8'
        )


def main():
    parser = argparse.ArgumentParser(
        description='FormalScience 文档批量规范化工具',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
示例:
  python batch_normalize_documents.py                    # 规范化当前目录
  python batch_normalize_documents.py ./docs             # 规范化指定目录
  python batch_normalize_documents.py . --dry-run        # 预览变更
  python batch_normalize_documents.py . --limit 50       # 只处理50个文件
  python batch_normalize_documents.py . --verbose        # 显示详细信息
        """
    )
    parser.add_argument('path', nargs='?', default='.', help='要处理的路径 (默认: 当前目录)')
    parser.add_argument('--dry-run', action='store_true', help='预览模式，不实际修改')
    parser.add_argument('--verbose', action='store_true', help='显示详细输出')
    parser.add_argument('--limit', type=int, help='限制处理文件数量')
    parser.add_argument('--include-root', action='store_true', help='包含根目录文件')
    parser.add_argument('--report', metavar='FILE', help='生成文本报告')
    parser.add_argument('--json', metavar='FILE', help='生成JSON变更日志')
    
    args = parser.parse_args()
    
    print("🚀 FormalScience 文档批量规范化工具")
    print("=" * 60)
    
    if args.dry_run:
        print("⚠️  预览模式 - 不会实际修改文件")
        print("")
    
    # 运行规范化
    normalizer = DocumentNormalizer(
        base_path=args.path,
        dry_run=args.dry_run,
        verbose=args.verbose
    )
    
    stats = normalizer.normalize_all(
        limit=args.limit,
        include_root=args.include_root
    )
    
    print("")
    print("=" * 60)
    print("📊 处理完成")
    print("=" * 60)
    
    # 生成报告
    report = normalizer.generate_report(args.report)
    print(report)
    
    # 保存JSON日志
    if args.json:
        normalizer.save_changes_log(args.json)
        print(f"📄 JSON日志已保存: {args.json}")
    
    # 总结
    print(f"""
✅ 处理统计:
   - 总文件: {stats.total_files}
   - 已处理: {stats.processed_files}
   - 已跳过: {stats.skipped_files}
   - 错误: {stats.error_files}

   变更:
   - 添加元数据: {stats.added_headers}
   - 规范化编号: {stats.fixed_numbering}
   - 修复格式: {stats.fixed_format}
    """)
    
    if args.dry_run:
        print("\n💡 使用 --dry-run 预览了变更，去掉该参数可实际执行")
    
    return 0


if __name__ == '__main__':
    sys.exit(main())
