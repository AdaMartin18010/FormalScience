#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FormalScience 文档质量检查工具
Document Quality Checker for FormalScience Project

功能：
1. 检测占位符（"- |- |- |- "等）
2. 检测章节完整性
3. 检测交叉引用格式
4. 检测元数据头格式
5. 生成质量报告

使用方法：
    python document_quality_checker.py [选项] <路径>

示例：
    python document_quality_checker.py Concept/
    python document_quality_checker.py --fix FormalRE/README.md
    python document_quality_checker.py --report output.md Concept/
"""

import os
import re
import sys
import argparse
import json
from pathlib import Path
from datetime import datetime
from typing import List, Dict, Tuple, Optional
from dataclasses import dataclass, asdict
from collections import defaultdict


@dataclass
class QualityIssue:
    """质量问题记录"""
    file_path: str
    line_number: int
    issue_type: str
    severity: str  # error, warning, info
    message: str
    suggestion: str = ""


@dataclass
class DocumentMetrics:
    """文档指标"""
    file_path: str
    title: str = ""
    has_metadata: bool = False
    has_toc: bool = False
    has_navigation: bool = False
    has_related_topics: bool = False
    has_mermaid_charts: bool = False
    placeholder_count: int = 0
    chapter_count: int = 0
    cross_ref_count: int = 0
    line_count: int = 0
    word_count: int = 0


class DocumentQualityChecker:
    """文档质量检查器"""
    
    # 占位符模式
    PLACEHOLDER_PATTERNS = [
        r'- \|- \|- \|- ',  # 表格占位符
        r'待补充',
        r'待完善',
        r'TODO',
        r'FIXME',
        r'XXX',
        r'\[待补充\]',
        r'\[TODO\]',
    ]
    
    # 必需的元数据字段
    REQUIRED_METADATA_FIELDS = [
        '文档版本',
        '最后更新',
        '主题',
    ]
    
    # 推荐的元数据字段
    RECOMMENDED_METADATA_FIELDS = [
        '文档规模',
        '阅读建议',
        '创建日期',
        '难度',
        '前置知识',
        '重要性',
    ]
    
    # 必需的章节（根据文档结构标准）
    RECOMMENDED_SECTIONS = [
        '## 📋 目录',
        '思维表征',
        '权威资源对标',
        '相关主题',
    ]
    
    def __init__(self, verbose: bool = False, fix_mode: bool = False):
        self.verbose = verbose
        self.fix_mode = fix_mode
        self.issues: List[QualityIssue] = []
        self.metrics: List[DocumentMetrics] = []
        self.checked_files: int = 0
        
    def log(self, message: str):
        """日志输出"""
        if self.verbose:
            print(f"[INFO] {message}")
    
    def check_file(self, file_path: str) -> Tuple[List[QualityIssue], DocumentMetrics]:
        """检查单个文件"""
        self.log(f"Checking: {file_path}")
        
        issues = []
        metrics = DocumentMetrics(file_path=file_path)
        
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
                lines = content.split('\n')
                metrics.line_count = len(lines)
                metrics.word_count = len(content.split())
        except Exception as e:
            issues.append(QualityIssue(
                file_path=file_path,
                line_number=0,
                issue_type="文件读取错误",
                severity="error",
                message=f"无法读取文件: {str(e)}"
            ))
            return issues, metrics
        
        # 检查元数据头
        issues.extend(self._check_metadata(content, lines, file_path, metrics))
        
        # 检查目录
        issues.extend(self._check_toc(content, lines, file_path, metrics))
        
        # 检查占位符
        issues.extend(self._check_placeholders(content, lines, file_path, metrics))
        
        # 检查章节完整性
        issues.extend(self._check_chapters(content, lines, file_path, metrics))
        
        # 检查交叉引用
        issues.extend(self._check_cross_references(content, lines, file_path, metrics))
        
        # 检查导航
        issues.extend(self._check_navigation(content, lines, file_path, metrics))
        
        # 检查相关主题
        issues.extend(self._check_related_topics(content, lines, file_path, metrics))
        
        # 检查思维表征
        issues.extend(self._check_mind_representations(content, lines, file_path, metrics))
        
        # 提取标题
        title_match = re.search(r'^# (.+)$', content, re.MULTILINE)
        if title_match:
            metrics.title = title_match.group(1).strip()
        
        self.checked_files += 1
        return issues, metrics
    
    def _check_metadata(self, content: str, lines: List[str], file_path: str, metrics: DocumentMetrics) -> List[QualityIssue]:
        """检查元数据头"""
        issues = []
        
        # 检查是否有元数据块
        metadata_pattern = r'> \*\*[^*]+\*\*:'
        if re.search(metadata_pattern, content):
            metrics.has_metadata = True
            
            # 检查必需的元数据字段
            for field in self.REQUIRED_METADATA_FIELDS:
                if field not in content:
                    issues.append(QualityIssue(
                        file_path=file_path,
                        line_number=1,
                        issue_type="元数据缺失",
                        severity="error",
                        message=f"缺少必需元数据字段: {field}",
                        suggestion=f"在文档头部添加: > **{field}**: 值"
                    ))
            
            # 检查推荐的元数据字段
            for field in self.RECOMMENDED_METADATA_FIELDS:
                if field not in content:
                    issues.append(QualityIssue(
                        file_path=file_path,
                        line_number=1,
                        issue_type="元数据建议",
                        severity="warning",
                        message=f"缺少推荐元数据字段: {field}",
                        suggestion=f"考虑添加: > **{field}**: 值"
                    ))
        else:
            issues.append(QualityIssue(
                file_path=file_path,
                line_number=1,
                issue_type="元数据缺失",
                severity="error",
                message="文档缺少元数据头",
                suggestion="在文档开头添加元数据块，参考标准模板"
            ))
        
        return issues
    
    def _check_toc(self, content: str, lines: List[str], file_path: str, metrics: DocumentMetrics) -> List[QualityIssue]:
        """检查目录"""
        issues = []
        
        if '## 📋 目录' in content or '## 目录' in content:
            metrics.has_toc = True
            
            # 检查目录是否有实际内容
            toc_match = re.search(r'## 📋 目录\n\n(.+?)(?=\n## |\Z)', content, re.DOTALL)
            if toc_match:
                toc_content = toc_match.group(1)
                if len(toc_content.strip()) < 50:
                    issues.append(QualityIssue(
                        file_path=file_path,
                        line_number=self._find_line_number(lines, '## 📋 目录'),
                        issue_type="目录内容不足",
                        severity="warning",
                        message="目录内容可能不完整",
                        suggestion="确保目录包含所有章节链接"
                    ))
        else:
            issues.append(QualityIssue(
                file_path=file_path,
                line_number=1,
                issue_type="目录缺失",
                severity="warning",
                message="文档缺少目录",
                suggestion="添加 '## 📋 目录' 章节"
            ))
        
        return issues
    
    def _check_placeholders(self, content: str, lines: List[str], file_path: str, metrics: DocumentMetrics) -> List[QualityIssue]:
        """检查占位符"""
        issues = []
        
        for pattern in self.PLACEHOLDER_PATTERNS:
            matches = list(re.finditer(pattern, content))
            for match in matches:
                line_num = content[:match.start()].count('\n') + 1
                issues.append(QualityIssue(
                    file_path=file_path,
                    line_number=line_num,
                    issue_type="占位符",
                    severity="warning",
                    message=f"发现占位符: {match.group()}",
                    suggestion="请补充实际内容"
                ))
                metrics.placeholder_count += 1
        
        return issues
    
    def _check_chapters(self, content: str, lines: List[str], file_path: str, metrics: DocumentMetrics) -> List[QualityIssue]:
        """检查章节完整性"""
        issues = []
        
        # 统计章节数
        chapter_pattern = r'^## \d+\.'
        chapters = re.findall(chapter_pattern, content, re.MULTILINE)
        metrics.chapter_count = len(chapters)
        
        # 检查推荐章节
        for section in self.RECOMMENDED_SECTIONS:
            if section not in content:
                issues.append(QualityIssue(
                    file_path=file_path,
                    line_number=1,
                    issue_type="章节建议",
                    severity="info",
                    message=f"缺少推荐章节: {section}",
                    suggestion=f"考虑添加 {section} 章节"
                ))
        
        # 检查章节编号连续性
        chapter_numbers = []
        for match in re.finditer(r'^## (\d+)\.', content, re.MULTILINE):
            chapter_numbers.append(int(match.group(1)))
        
        if chapter_numbers:
            expected = list(range(min(chapter_numbers), max(chapter_numbers) + 1))
            missing = set(expected) - set(chapter_numbers)
            if missing:
                issues.append(QualityIssue(
                    file_path=file_path,
                    line_number=1,
                    issue_type="章节编号不连续",
                    severity="warning",
                    message=f"缺少章节编号: {sorted(missing)}",
                    suggestion="检查并修复章节编号"
                ))
        
        return issues
    
    def _check_cross_references(self, content: str, lines: List[str], file_path: str, metrics: DocumentMetrics) -> List[QualityIssue]:
        """检查交叉引用"""
        issues = []
        
        # 查找所有Markdown链接
        link_pattern = r'\[([^\]]+)\]\(([^)]+)\)'
        links = re.findall(link_pattern, content)
        metrics.cross_ref_count = len(links)
        
        for text, url in links:
            # 检查内部链接
            if url.endswith('.md') and not url.startswith('http'):
                # 检查相对路径
                if url.startswith('./') or url.startswith('../') or not url.startswith('/'):
                    base_dir = os.path.dirname(file_path)
                    target_path = os.path.normpath(os.path.join(base_dir, url))
                    
                    if not os.path.exists(target_path):
                        line_num = self._find_line_number_with_text(lines, f'[{text}]({url})')
                        issues.append(QualityIssue(
                            file_path=file_path,
                            line_number=line_num,
                            issue_type="链接失效",
                            severity="error",
                            message=f"链接指向的文件不存在: {url}",
                            suggestion=f"检查路径或创建目标文件: {target_path}"
                        ))
        
        return issues
    
    def _check_navigation(self, content: str, lines: List[str], file_path: str, metrics: DocumentMetrics) -> List[QualityIssue]:
        """检查导航"""
        issues = []
        
        if '**导航**' in content or '导航：' in content:
            metrics.has_navigation = True
            
            # 检查导航格式
            if '←' not in content or '→' not in content:
                issues.append(QualityIssue(
                    file_path=file_path,
                    line_number=self._find_line_number(lines, '导航'),
                    issue_type="导航格式问题",
                    severity="warning",
                    message="导航缺少上一节或下一节链接",
                    suggestion="使用格式: [← 上一节](url) | [下一节 →](url)"
                ))
        else:
            issues.append(QualityIssue(
                file_path=file_path,
                line_number=len(lines),
                issue_type="导航缺失",
                severity="warning",
                message="文档缺少导航",
                suggestion="在文档末尾添加导航链接"
            ))
        
        return issues
    
    def _check_related_topics(self, content: str, lines: List[str], file_path: str, metrics: DocumentMetrics) -> List[QualityIssue]:
        """检查相关主题"""
        issues = []
        
        if '相关主题' in content:
            metrics.has_related_topics = True
            
            # 检查是否有实际链接
            related_section = re.search(r'##.*相关主题.*\n\n(.+?)(?=\n## |\Z)', content, re.DOTALL)
            if related_section:
                links = re.findall(r'\[([^\]]+)\]\([^)]+\)', related_section.group(1))
                if len(links) < 2:
                    issues.append(QualityIssue(
                        file_path=file_path,
                        line_number=self._find_line_number(lines, '相关主题'),
                        issue_type="相关主题不足",
                        severity="info",
                        message="相关主题链接较少",
                        suggestion="建议添加至少3个相关主题链接"
                    ))
        else:
            issues.append(QualityIssue(
                file_path=file_path,
                line_number=len(lines),
                issue_type="相关主题缺失",
                severity="warning",
                message="文档缺少相关主题章节",
                suggestion="添加 ## 相关主题 章节"
            ))
        
        return issues
    
    def _check_mind_representations(self, content: str, lines: List[str], file_path: str, metrics: DocumentMetrics) -> List[QualityIssue]:
        """检查思维表征"""
        issues = []
        
        # 检查Mermaid图表
        if '```mermaid' in content:
            metrics.has_mermaid_charts = True
            
            # 检查思维表征章节
            if '思维表征' not in content:
                issues.append(QualityIssue(
                    file_path=file_path,
                    line_number=1,
                    issue_type="思维表征章节缺失",
                    severity="info",
                    message="文档有Mermaid图表但缺少'思维表征'章节",
                    suggestion="将Mermaid图表整理到'思维表征'章节"
                ))
        
        # 检查是否包含推荐的6种图表
        recommended_charts = [
            ('概念关系网络图', '概念关系'),
            ('论证逻辑路径图', '论证逻辑'),
            ('概念属性矩阵', '属性矩阵'),
            ('外延内涵分析图', '外延内涵'),
            ('理论发展脉络图', '发展脉络'),
            ('跨模块关联图', '跨模块'),
        ]
        
        if '思维表征' in content:
            for chart_name, keyword in recommended_charts:
                if keyword not in content:
                    issues.append(QualityIssue(
                        file_path=file_path,
                        line_number=1,
                        issue_type="思维表征缺失",
                        severity="info",
                        message=f"缺少{chart_name}",
                        suggestion=f"添加 {chart_name}"
                    ))
        
        return issues
    
    def _find_line_number(self, lines: List[str], text: str) -> int:
        """查找文本所在行号"""
        for i, line in enumerate(lines, 1):
            if text in line:
                return i
        return 0
    
    def _find_line_number_with_text(self, lines: List[str], text: str) -> int:
        """查找精确文本所在行号"""
        for i, line in enumerate(lines, 1):
            if text in line:
                return i
        return 0
    
    def check_directory(self, directory: str, recursive: bool = True) -> Tuple[List[QualityIssue], List[DocumentMetrics]]:
        """检查整个目录"""
        all_issues = []
        all_metrics = []
        
        path = Path(directory)
        pattern = '**/*.md' if recursive else '*.md'
        
        for md_file in path.glob(pattern):
            if '.git' in str(md_file):
                continue
            
            issues, metrics = self.check_file(str(md_file))
            all_issues.extend(issues)
            all_metrics.append(metrics)
        
        return all_issues, all_metrics
    
    def generate_report(self, issues: List[QualityIssue], metrics: List[DocumentMetrics], 
                       output_format: str = 'console', output_file: Optional[str] = None) -> str:
        """生成质量报告"""
        
        # 统计
        error_count = sum(1 for i in issues if i.severity == 'error')
        warning_count = sum(1 for i in issues if i.severity == 'warning')
        info_count = sum(1 for i in issues if i.severity == 'info')
        
        if output_format == 'json':
            report = {
                'summary': {
                    'checked_files': self.checked_files,
                    'total_issues': len(issues),
                    'errors': error_count,
                    'warnings': warning_count,
                    'infos': info_count,
                    'generated_at': datetime.now().isoformat()
                },
                'issues': [asdict(i) for i in issues],
                'metrics': [asdict(m) for m in metrics]
            }
            return json.dumps(report, ensure_ascii=False, indent=2)
        
        elif output_format == 'markdown':
            lines = [
                "# 文档质量检查报告",
                "",
                f"> **生成时间**: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
                f"> **检查文件数**: {self.checked_files}",
                "",
                "---",
                "",
                "## 📊 质量概览",
                "",
                f"| 指标 | 数值 |",
                f"|------|------|",
                f"| 检查文件数 | {self.checked_files} |",
                f"| 总问题数 | {len(issues)} |",
                f"| 🔴 错误 | {error_count} |",
                f"| 🟡 警告 | {warning_count} |",
                f"| 🔵 建议 | {info_count} |",
                "",
                "---",
                "",
                "## 📋 问题列表",
                "",
            ]
            
            # 按严重程度分组
            severity_order = {'error': 0, 'warning': 1, 'info': 2}
            sorted_issues = sorted(issues, key=lambda x: severity_order.get(x.severity, 3))
            
            current_file = None
            for issue in sorted_issues:
                if issue.file_path != current_file:
                    current_file = issue.file_path
                    lines.append(f"### {current_file}")
                    lines.append("")
                
                severity_emoji = {'error': '🔴', 'warning': '🟡', 'info': '🔵'}.get(issue.severity, '⚪')
                lines.append(f"- {severity_emoji} **行{issue.line_number}** [{issue.issue_type}]: {issue.message}")
                if issue.suggestion:
                    lines.append(f"  - 💡 建议: {issue.suggestion}")
                lines.append("")
            
            lines.extend([
                "---",
                "",
                "## 📈 文档指标",
                "",
                "| 文件 | 标题 | 元数据 | 目录 | 导航 | 章节数 | 链接数 | 占位符 |",
                "|------|------|--------|------|------|--------|--------|--------|",
            ])
            
            for m in metrics:
                check = lambda x: '✅' if x else '❌'
                lines.append(
                    f"| {m.file_path} | {m.title[:30] if m.title else '-'}... | "
                    f"{check(m.has_metadata)} | {check(m.has_toc)} | {check(m.has_navigation)} | "
                    f"{m.chapter_count} | {m.cross_ref_count} | {m.placeholder_count} |"
                )
            
            lines.append("")
            lines.append("---")
            lines.append("")
            lines.append("**报告生成**: FormalScience 文档质量检查工具")
            
            return '\n'.join(lines)
        
        else:  # console format
            lines = [
                "=" * 60,
                "文档质量检查报告",
                "=" * 60,
                "",
                f"检查文件数: {self.checked_files}",
                f"总问题数: {len(issues)}",
                f"  🔴 错误: {error_count}",
                f"  🟡 警告: {warning_count}",
                f"  🔵 建议: {info_count}",
                "",
                "-" * 60,
                "问题详情:",
                "-" * 60,
            ]
            
            current_file = None
            for issue in issues:
                if issue.file_path != current_file:
                    current_file = issue.file_path
                    lines.append(f"\n📄 {current_file}")
                
                severity_emoji = {'error': '🔴', 'warning': '🟡', 'info': '🔵'}.get(issue.severity, '⚪')
                lines.append(f"  {severity_emoji} 行{issue.line_number}: [{issue.issue_type}] {issue.message}")
                if issue.suggestion:
                    lines.append(f"     💡 {issue.suggestion}")
            
            return '\n'.join(lines)


def normalize_metadata(file_path: str, template_path: Optional[str] = None) -> bool:
    """
    标准化文档元数据头
    
    Args:
        file_path: 要处理的文件路径
        template_path: 标准模板路径（可选）
    
    Returns:
        是否成功
    """
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # 检查是否已有元数据
        if '> **文档版本**' in content or '> **版本**' in content:
            print(f"文件已有元数据: {file_path}")
            return True
        
        # 获取标题
        title_match = re.search(r'^# (.+)$', content, re.MULTILINE)
        title = title_match.group(1) if title_match else "未命名文档"
        
        # 创建标准元数据头
        today = datetime.now().strftime('%Y-%m-%d')
        metadata = f"""# {title}

> **文档版本**: v1.0.0
> **创建日期**: {today}
> **最后更新**: {today}
> **文档规模**: 估算中 | 待评估
> **主题**: 待补充
> **难度**: ⭐⭐⭐
> **前置知识**: 待补充
> **重要性**: ⭐⭐⭐⭐⭐
> **阅读建议**: 本文档适合有相关基础的读者

---

"""
        
        # 替换或插入元数据
        if title_match:
            new_content = content[:title_match.end()] + '\n' + metadata.split('\n', 1)[1] + content[title_match.end():]
        else:
            new_content = metadata + content
        
        with open(file_path, 'w', encoding='utf-8') as f:
            f.write(new_content)
        
        print(f"✅ 已标准化: {file_path}")
        return True
        
    except Exception as e:
        print(f"❌ 处理失败 {file_path}: {e}")
        return False


def main():
    parser = argparse.ArgumentParser(
        description='FormalScience 文档质量检查工具',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
示例:
  %(prog)s Concept/                          # 检查整个目录
  %(prog)s --recursive FormalRE/             # 递归检查
  %(prog)s --format markdown --output report.md Concept/  # 生成Markdown报告
  %(prog)s --fix Concept/README.md           # 修复单个文件元数据
  %(prog)s --normalize Concept/              # 标准化所有文件元数据
        """
    )
    
    parser.add_argument('path', help='要检查的文件或目录路径')
    parser.add_argument('-r', '--recursive', action='store_true', 
                       help='递归检查子目录')
    parser.add_argument('-f', '--format', choices=['console', 'markdown', 'json'],
                       default='console', help='报告格式')
    parser.add_argument('-o', '--output', help='输出文件路径')
    parser.add_argument('-v', '--verbose', action='store_true',
                       help='详细输出')
    parser.add_argument('--fix', action='store_true',
                       help='尝试自动修复问题（仅元数据）')
    parser.add_argument('--normalize', action='store_true',
                       help='标准化所有文件的元数据头')
    parser.add_argument('--template', 
                       default='docs/Refactor/.templates/standard_document_template.md',
                       help='标准模板路径')
    
    args = parser.parse_args()
    
    # 标准化模式
    if args.normalize:
        path = Path(args.path)
        if path.is_file():
            normalize_metadata(str(path), args.template)
        else:
            pattern = '**/*.md' if args.recursive else '*.md'
            for md_file in path.glob(pattern):
                if '.git' not in str(md_file):
                    normalize_metadata(str(md_file), args.template)
        return
    
    # 检查模式
    checker = DocumentQualityChecker(verbose=args.verbose, fix_mode=args.fix)
    
    if os.path.isfile(args.path):
        issues, metrics_list = checker.check_file(args.path)
        all_issues = issues
        all_metrics = [metrics_list]
    else:
        all_issues, all_metrics = checker.check_directory(args.path, args.recursive)
    
    # 生成报告
    report = checker.generate_report(all_issues, all_metrics, args.format, args.output)
    
    if args.output:
        with open(args.output, 'w', encoding='utf-8') as f:
            f.write(report)
        print(f"✅ 报告已保存: {args.output}")
    else:
        print(report)
    
    # 如果有错误，返回非零状态码
    error_count = sum(1 for i in all_issues if i.severity == 'error')
    if error_count > 0:
        sys.exit(1)


if __name__ == '__main__':
    main()
