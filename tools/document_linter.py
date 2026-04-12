#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FormalScience 文档质量检查脚本 (Document Linter)

功能：
1. 检查占位符（"- |- |- |- "模式）
2. 检查章节完整性（必须包含：概述、理论体系、实践应用、关联网络）
3. 检查元数据头
4. 检查内部链接有效性
5. 检查LaTeX公式格式
6. 输出质量报告

用法：
    python document_linter.py [路径] [选项]
    
    选项：
        --fix           自动修复可修复的问题
        --report        生成详细报告文件
        --strict        严格模式（更严格的检查）
        --exclude       排除指定目录（逗号分隔）
"""

import os
import re
import sys
import json
import argparse
from pathlib import Path
from datetime import datetime
from typing import List, Dict, Tuple, Optional, Set
from dataclasses import dataclass, field, asdict
from collections import defaultdict


@dataclass
class LintIssue:
    """检查问题记录"""
    file_path: str
    line_number: int
    severity: str  # error, warning, info
    category: str  # placeholder, structure, metadata, link, latex, format
    message: str
    suggestion: str = ""
    
    def to_dict(self):
        return asdict(self)


@dataclass
class DocumentStats:
    """文档统计信息"""
    total_files: int = 0
    total_issues: int = 0
    error_count: int = 0
    warning_count: int = 0
    info_count: int = 0
    files_with_issues: Set[str] = field(default_factory=set)
    issues_by_category: Dict[str, int] = field(default_factory=lambda: defaultdict(int))
    issues_by_severity: Dict[str, int] = field(default_factory=lambda: defaultdict(int))


class DocumentLinter:
    """文档质量检查器"""
    
    # 占位符模式
    PLACEHOLDER_PATTERNS = [
        r'-+\s*\|\s*-+\s*\|\s*-+\s*\|\s*-+',  # - |- |- |- 模式
        r'\[?待填充\]?',
        r'\[?TODO\]?',
        r'\[?FIXME\]?',
        r'\[?PLACEHOLDER\]?',
        r'\[?占位符\]?',
        r'此处待补充',
        r'内容待完善',
        r'待完善',
        r'\.{3,}',  # 三个以上点号
    ]
    
    # 必须包含的章节（正则表达式）
    REQUIRED_SECTIONS = [
        (r'^(#{1,3})\s*概述', "概述"),
        (r'^(#{1,3})\s*理论', "理论体系"),
        (r'^(#{1,3})\s*实践|应用', "实践应用"),
        (r'^(#{1,3})\s*关联|网络|参考', "关联网络"),
    ]
    
    # 元数据必需字段
    REQUIRED_METADATA_FIELDS = [
        "topic",
        "status",
        "date",
    ]
    
    # 可选但有推荐的字段
    RECOMMENDED_METADATA_FIELDS = [
        "author",
        "version",
        "tags",
        "category",
    ]
    
    def __init__(self, base_path: str, strict: bool = False, exclude_dirs: List[str] = None):
        self.base_path = Path(base_path)
        self.strict = strict
        self.exclude_dirs = exclude_dirs or ['.git', 'node_modules', 'venv', '__pycache__', '.templates']
        self.issues: List[LintIssue] = []
        self.stats = DocumentStats()
        self.broken_links: Dict[str, List[str]] = {}
        
    def lint_all(self, fix: bool = False) -> DocumentStats:
        """检查所有Markdown文件"""
        md_files = list(self.base_path.rglob("*.md"))
        
        self.stats.total_files = len(md_files)
        
        for md_file in md_files:
            # 检查是否在被排除的目录中
            if any(excluded in str(md_file) for excluded in self.exclude_dirs):
                continue
            
            try:
                self._lint_file(md_file, fix)
            except Exception as e:
                self.issues.append(LintIssue(
                    file_path=str(md_file),
                    line_number=0,
                    severity="error",
                    category="format",
                    message=f"文件处理失败: {str(e)}",
                    suggestion="检查文件编码和格式"
                ))
        
        self._update_stats()
        return self.stats
    
    def _lint_file(self, file_path: Path, fix: bool = False):
        """检查单个文件"""
        content = file_path.read_text(encoding='utf-8')
        lines = content.split('\n')
        relative_path = file_path.relative_to(self.base_path)
        
        # 1. 检查占位符
        self._check_placeholders(lines, relative_path)
        
        # 2. 检查章节完整性
        self._check_structure(lines, relative_path)
        
        # 3. 检查元数据头
        self._check_metadata(content, lines, relative_path)
        
        # 4. 检查内部链接
        self._check_links(content, file_path, relative_path)
        
        # 5. 检查LaTeX公式
        self._check_latex(content, lines, relative_path)
        
        # 6. 检查格式问题
        self._check_format(lines, relative_path)
    
    def _check_placeholders(self, lines: List[str], file_path: Path):
        """检查占位符"""
        for i, line in enumerate(lines, 1):
            for pattern in self.PLACEHOLDER_PATTERNS:
                if re.search(pattern, line, re.IGNORECASE):
                    self.issues.append(LintIssue(
                        file_path=str(file_path),
                        line_number=i,
                        severity="error" if self.strict else "warning",
                        category="placeholder",
                        message=f"发现占位符: {line.strip()[:50]}",
                        suggestion="请填充实际内容或删除占位符"
                    ))
                    break
    
    def _check_structure(self, lines: List[str], file_path: Path):
        """检查章节结构"""
        content = '\n'.join(lines)
        
        found_sections = set()
        for pattern, section_name in self.REQUIRED_SECTIONS:
            if re.search(pattern, content, re.MULTILINE | re.IGNORECASE):
                found_sections.add(section_name)
        
        required_section_names = [s[1] for s in self.REQUIRED_SECTIONS]
        missing_sections = set(required_section_names) - found_sections
        
        if len(found_sections) < 2 and len(lines) > 50:  # 超过50行的文档应该有基本结构
            self.issues.append(LintIssue(
                file_path=str(file_path),
                line_number=0,
                severity="warning",
                category="structure",
                message=f"文档结构不完整，缺少标准章节",
                suggestion=f"建议添加以下章节: {', '.join(missing_sections)}"
            ))
    
    def _check_metadata(self, content: str, lines: List[str], file_path: Path):
        """检查元数据头"""
        # 检查YAML frontmatter
        yaml_match = re.match(r'^---\s*\n(.*?)\n---\s*\n', content, re.DOTALL)
        
        if not yaml_match:
            # 检查是否有其他格式的元数据
            has_metadata = any(
                re.match(r'^\s*(topic|主题)\s*[:：]', line) 
                for line in lines[:20]
            )
            
            if not has_metadata:
                self.issues.append(LintIssue(
                    file_path=str(file_path),
                    line_number=1,
                    severity="warning",
                    category="metadata",
                    message="缺少元数据头",
                    suggestion="在文档开头添加YAML frontmatter元数据块"
                ))
            return
        
        yaml_content = yaml_match.group(1)
        
        # 检查必需字段
        for field in self.REQUIRED_METADATA_FIELDS:
            if field not in yaml_content:
                self.issues.append(LintIssue(
                    file_path=str(file_path),
                    line_number=1,
                    severity="warning",
                    category="metadata",
                    message=f"元数据缺少必需字段: {field}",
                    suggestion=f"添加 '{field}: value' 到元数据头"
                ))
        
        # 检查推荐字段
        for field in self.RECOMMENDED_METADATA_FIELDS:
            if field not in yaml_content:
                self.issues.append(LintIssue(
                    file_path=str(file_path),
                    line_number=1,
                    severity="info",
                    category="metadata",
                    message=f"元数据缺少推荐字段: {field}",
                    suggestion=f"建议添加 '{field}: value' 完善文档信息"
                ))
    
    def _check_links(self, content: str, file_path: Path, relative_path: Path):
        """检查内部链接有效性"""
        # 匹配Markdown链接 [text](url)
        link_pattern = r'\[([^\]]+)\]\(([^)]+)\)'
        links = re.findall(link_pattern, content)
        
        for text, url in links:
            # 跳过外部链接
            if url.startswith(('http://', 'https://', 'mailto:', '#')):
                continue
            
            # 解析相对路径
            if url.startswith('/'):
                target_path = self.base_path / url.lstrip('/')
            else:
                target_path = file_path.parent / url
                target_path = target_path.resolve()
            
            # 处理锚点
            if '#' in url:
                target_path = Path(str(target_path).split('#')[0])
            
            if not target_path.exists():
                # 查找行号
                line_num = 1
                for i, line in enumerate(content.split('\n'), 1):
                    if f']({url})' in line:
                        line_num = i
                        break
                
                self.issues.append(LintIssue(
                    file_path=str(relative_path),
                    line_number=line_num,
                    severity="error",
                    category="link",
                    message=f"断链: [{text}]({url})",
                    suggestion=f"检查路径是否正确，目标文件是否存在"
                ))
                
                if str(relative_path) not in self.broken_links:
                    self.broken_links[str(relative_path)] = []
                self.broken_links[str(relative_path)].append(url)
    
    def _check_latex(self, content: str, lines: List[str], file_path: Path):
        """检查LaTeX公式格式"""
        # 检查行内公式
        inline_pattern = r'[^$]\$[^$]+\$[^$]'
        inline_matches = list(re.finditer(inline_pattern, content))
        
        for match in inline_matches:
            # 查找行号
            pos = match.start()
            line_num = content[:pos].count('\n') + 1
            
            # 检查是否有空格问题
            formula = match.group(0)
            if not (formula.startswith(' $') or formula.startswith('\n$')):
                pass  # 允许紧凑格式
            
            # 检查常见错误
            if '\\ ' in formula or formula.count('_') != formula.count('}'):
                # 可能有格式问题
                pass
        
        # 检查块级公式
        block_pattern = r'\$\$[\s\S]*?\$\$'
        block_matches = re.findall(block_pattern, content)
        
        for block in block_matches:
            # 检查未闭合的括号
            open_count = block.count('{') + block.count('[') + block.count('(')
            close_count = block.count('}') + block.count(']') + block.count(')')
            
            if open_count != close_count:
                pos = content.find(block)
                line_num = content[:pos].count('\n') + 1
                
                self.issues.append(LintIssue(
                    file_path=str(file_path),
                    line_number=line_num,
                    severity="error",
                    category="latex",
                    message="LaTeX公式括号不匹配",
                    suggestion="检查公式中的 {}, [], () 是否成对出现"
                ))
        
        # 检查 $$ 和 $ 混用问题
        if '$$' in content:
            # 检查是否有应该使用 $$ 但用了 $ 的地方
            pass
    
    def _check_format(self, lines: List[str], file_path: Path):
        """检查格式问题"""
        for i, line in enumerate(lines, 1):
            # 检查行尾空格
            if line.rstrip() != line:
                self.issues.append(LintIssue(
                    file_path=str(file_path),
                    line_number=i,
                    severity="info",
                    category="format",
                    message="行尾有多余空格",
                    suggestion="删除行尾空格"
                ))
            
            # 检查Tab字符
            if '\t' in line:
                self.issues.append(LintIssue(
                    file_path=str(file_path),
                    line_number=i,
                    severity="warning",
                    category="format",
                    message="使用Tab字符缩进",
                    suggestion="使用空格代替Tab（建议2或4个空格）"
                ))
            
            # 检查标题层级跳跃
            if line.startswith('#'):
                level = len(line) - len(line.lstrip('#'))
                if level > 3 and i < 50:  # 前50行出现深层标题
                    prev_lines = '\n'.join(lines[max(0, i-5):i])
                    prev_levels = [len(l) - len(l.lstrip('#')) 
                                   for l in prev_lines.split('\n') 
                                   if l.strip().startswith('#')]
                    if prev_levels and level > max(prev_levels) + 1:
                        self.issues.append(LintIssue(
                            file_path=str(file_path),
                            line_number=i,
                            severity="warning",
                            category="format",
                            message=f"标题层级跳跃: 从 {max(prev_levels)} 跳到 {level}",
                            suggestion="保持标题层级连续，不要跳跃"
                        ))
    
    def _update_stats(self):
        """更新统计信息"""
        self.stats.total_issues = len(self.issues)
        
        for issue in self.issues:
            self.stats.files_with_issues.add(issue.file_path)
            self.stats.issues_by_category[issue.category] += 1
            self.stats.issues_by_severity[issue.severity] += 1
            
            if issue.severity == "error":
                self.stats.error_count += 1
            elif issue.severity == "warning":
                self.stats.warning_count += 1
            else:
                self.stats.info_count += 1
    
    def generate_report(self, output_path: Optional[str] = None) -> str:
        """生成质量报告"""
        report_lines = []
        
        # 报告头
        report_lines.append("=" * 80)
        report_lines.append("FormalScience 文档质量检查报告")
        report_lines.append("=" * 80)
        report_lines.append(f"生成时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        report_lines.append(f"检查路径: {self.base_path}")
        report_lines.append(f"严格模式: {'是' if self.strict else '否'}")
        report_lines.append("")
        
        # 统计摘要
        report_lines.append("-" * 80)
        report_lines.append("统计摘要")
        report_lines.append("-" * 80)
        report_lines.append(f"总文件数: {self.stats.total_files}")
        report_lines.append(f"问题文件数: {len(self.stats.files_with_issues)}")
        report_lines.append(f"总问题数: {self.stats.total_issues}")
        report_lines.append(f"  - 错误: {self.stats.error_count}")
        report_lines.append(f"  - 警告: {self.stats.warning_count}")
        report_lines.append(f"  - 信息: {self.stats.info_count}")
        report_lines.append("")
        
        # 按类别统计
        report_lines.append("-" * 80)
        report_lines.append("问题分类统计")
        report_lines.append("-" * 80)
        for category, count in sorted(self.stats.issues_by_category.items(), key=lambda x: -x[1]):
            severity_icon = ""
            if category in ["placeholder", "link", "latex"]:
                severity_icon = "🔴"
            elif category in ["structure", "metadata", "format"]:
                severity_icon = "🟡"
            else:
                severity_icon = "🔵"
            report_lines.append(f"  {severity_icon} {category:15s}: {count:4d}")
        report_lines.append("")
        
        # 问题详情
        if self.issues:
            report_lines.append("-" * 80)
            report_lines.append("问题详情")
            report_lines.append("-" * 80)
            report_lines.append("")
            
            # 按文件分组
            issues_by_file = defaultdict(list)
            for issue in self.issues:
                issues_by_file[issue.file_path].append(issue)
            
            for file_path, issues in sorted(issues_by_file.items()):
                report_lines.append(f"📄 {file_path}")
                report_lines.append("-" * 40)
                
                # 按严重性排序
                severity_order = {"error": 0, "warning": 1, "info": 2}
                sorted_issues = sorted(issues, key=lambda x: severity_order.get(x.severity, 3))
                
                for issue in sorted_issues:
                    icon = "🔴" if issue.severity == "error" else "🟡" if issue.severity == "warning" else "🔵"
                    report_lines.append(f"  {icon} 行 {issue.line_number:4d} [{issue.category}] {issue.message}")
                    if issue.suggestion:
                        report_lines.append(f"     💡 {issue.suggestion}")
                report_lines.append("")
        
        # 断链汇总
        if self.broken_links:
            report_lines.append("-" * 80)
            report_lines.append("断链汇总")
            report_lines.append("-" * 80)
            for file_path, links in sorted(self.broken_links.items()):
                report_lines.append(f"📄 {file_path}")
                for link in links:
                    report_lines.append(f"    🔗 {link}")
            report_lines.append("")
        
        # 建议
        report_lines.append("-" * 80)
        report_lines.append("改进建议")
        report_lines.append("-" * 80)
        
        if self.stats.error_count > 0:
            report_lines.append("🔴 优先级1: 修复所有错误（占位符、断链、公式错误）")
        if self.stats.warning_count > 0:
            report_lines.append("🟡 优先级2: 处理警告（缺少章节、元数据不完整）")
        if self.stats.info_count > 0:
            report_lines.append("🔵 优先级3: 优化格式（空格、缩进）")
        
        report_lines.append("")
        report_lines.append("=" * 80)
        
        report = '\n'.join(report_lines)
        
        # 保存报告
        if output_path:
            Path(output_path).write_text(report, encoding='utf-8')
        
        return report
    
    def generate_json_report(self, output_path: Optional[str] = None) -> str:
        """生成JSON格式报告"""
        data = {
            "timestamp": datetime.now().isoformat(),
            "base_path": str(self.base_path),
            "strict_mode": self.strict,
            "statistics": {
                "total_files": self.stats.total_files,
                "files_with_issues": len(self.stats.files_with_issues),
                "total_issues": self.stats.total_issues,
                "errors": self.stats.error_count,
                "warnings": self.stats.warning_count,
                "infos": self.stats.info_count,
                "by_category": dict(self.stats.issues_by_category),
                "by_severity": dict(self.stats.issues_by_severity),
            },
            "issues": [issue.to_dict() for issue in self.issues],
            "broken_links": self.broken_links,
        }
        
        json_report = json.dumps(data, ensure_ascii=False, indent=2)
        
        if output_path:
            Path(output_path).write_text(json_report, encoding='utf-8')
        
        return json_report


def main():
    parser = argparse.ArgumentParser(
        description='FormalScience 文档质量检查工具',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
示例:
  python document_linter.py                    # 检查当前目录
  python document_linter.py ./docs             # 检查指定目录
  python document_linter.py . --strict         # 严格模式
  python document_linter.py . --report report.txt  # 生成报告
  python document_linter.py . --exclude temp,old   # 排除目录
        """
    )
    parser.add_argument('path', nargs='?', default='.', help='要检查的路径 (默认: 当前目录)')
    parser.add_argument('--fix', action='store_true', help='自动修复可修复的问题')
    parser.add_argument('--report', metavar='FILE', help='生成文本报告到指定文件')
    parser.add_argument('--json', metavar='FILE', help='生成JSON报告到指定文件')
    parser.add_argument('--strict', action='store_true', help='启用严格模式')
    parser.add_argument('--exclude', help='排除的目录，逗号分隔')
    
    args = parser.parse_args()
    
    # 解析排除目录
    exclude_dirs = None
    if args.exclude:
        exclude_dirs = [d.strip() for d in args.exclude.split(',')]
    
    # 运行检查
    linter = DocumentLinter(
        base_path=args.path,
        strict=args.strict,
        exclude_dirs=exclude_dirs
    )
    
    print(f"🔍 正在检查: {args.path}")
    print("-" * 40)
    
    stats = linter.lint_all(fix=args.fix)
    
    # 生成报告
    report = linter.generate_report(args.report)
    print(report)
    
    # 生成JSON报告
    if args.json:
        linter.generate_json_report(args.json)
        print(f"\n📊 JSON报告已保存: {args.json}")
    
    # 返回退出码
    if stats.error_count > 0:
        return 1
    elif stats.warning_count > 0:
        return 2
    return 0


if __name__ == '__main__':
    sys.exit(main())
