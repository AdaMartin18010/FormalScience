#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
格式验证脚本 (validate_format.py)

功能说明:
-----------
该脚本用于验证 Markdown 文档的格式规范性，包括:
- 检查 Markdown 语法错误
- 验证标题层级连续性
- 检查代码块完整性
- 检测常见的格式问题
- 验证 YAML Front Matter（可选）
- 检查表格格式

使用方法:
-----------
1. 验证当前目录下的所有 Markdown 文件:
   python validate_format.py

2. 验证指定目录:
   python validate_format.py -d /path/to/docs

3. 生成详细的 JSON 报告:
   python validate_format.py -o report.json -f json

4. 自动修复一些简单问题:
   python validate_format.py --fix

5. 检查特定规则:
   python validate_format.py --rules heading-level, code-block

参数说明:
-----------
-d, --directory     指定要验证的目录（默认: 当前目录）
-o, --output        输出报告文件路径
-f, --format        报告格式: text, json, html（默认: text）
--fix               尝试自动修复一些问题
--rules             指定要检查的规则（逗号分隔）
--strict            严格模式（更严格的检查）
--exclude           排除特定路径（可多次使用）
-v, --verbose       显示详细输出
-h, --help          显示帮助信息

验证规则:
-----------
- heading-level: 标题层级连续性
- code-block: 代码块完整性
- link-format: 链接格式
- table-format: 表格格式
- front-matter: YAML Front Matter
- whitespace: 空白字符
- line-length: 行长度限制

作者: FormalScience 文档工具链
版本: 1.0.0
"""

import argparse
import json
import os
import re
import sys
from dataclasses import dataclass, field, asdict
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple, Any


@dataclass
class ValidationIssue:
    """验证问题"""
    file_path: str
    line_number: int
    rule: str
    severity: str  # 'error', 'warning', 'info'
    message: str
    suggestion: Optional[str] = None


@dataclass
class FileValidationResult:
    """单个文件的验证结果"""
    file_path: str
    issues: List[ValidationIssue] = field(default_factory=list)
    passed: bool = True


@dataclass
class ValidationReport:
    """验证报告"""
    scan_time: str = ""
    base_directory: str = ""
    total_files: int = 0
    passed_files: int = 0
    failed_files: int = 0
    total_issues: int = 0
    errors: int = 0
    warnings: int = 0
    infos: int = 0
    results: List[FileValidationResult] = field(default_factory=list)
    rules_checked: List[str] = field(default_factory=list)


class FormatValidator:
    """Markdown 格式验证器"""
    
    # 所有可用规则
    ALL_RULES = [
        'heading-level',
        'code-block',
        'link-format',
        'table-format',
        'front-matter',
        'whitespace',
        'line-length',
        'list-format',
        'image-alt',
    ]
    
    # 正则表达式模式
    HEADING_PATTERN = re.compile(r'^(#{1,6})\s+(.+)$')
    CODE_BLOCK_START = re.compile(r'^```(\w*)\s*$')
    CODE_BLOCK_END = re.compile(r'^```\s*$')
    FRONT_MATTER_START = re.compile(r'^---\s*$')
    LINK_PATTERN = re.compile(r'\[([^\]]*)\]\(([^)]+)\)')
    IMAGE_PATTERN = re.compile(r'!\[([^\]]*)\]\(([^)]+)\)')
    TABLE_ROW = re.compile(r'^(\|[^|]+)+\|\s*$')
    TABLE_SEPARATOR = re.compile(r'^(\|:?-+:?)++\|\s*$')
    LIST_ITEM = re.compile(r'^(\s*)([-*+]|\d+\.)\s+(.+)$')
    WHITESPACE_LINE = re.compile(r'^[\t ]+\s*$')
    TRAILING_WHITESPACE = re.compile(r'[\t ]+$')
    
    def __init__(self, base_dir: Path, rules: Optional[List[str]] = None,
                 strict: bool = False, exclude_paths: Optional[List[str]] = None,
                 max_line_length: int = 120):
        """
        初始化格式验证器
        
        Args:
            base_dir: 基础文档目录
            rules: 要检查的规则列表
            strict: 是否使用严格模式
            exclude_paths: 要排除的路径列表
            max_line_length: 最大行长度
        """
        self.base_dir = Path(base_dir).resolve()
        self.rules = rules or self.ALL_RULES
        self.strict = strict
        self.exclude_paths = exclude_paths or []
        self.max_line_length = max_line_length
        self.report = ValidationReport()
        self.fixable_issues: List[Tuple[Path, int, str, str]] = []  # 可修复的问题
        
    def _should_exclude(self, path: Path) -> bool:
        """检查路径是否应该被排除"""
        path_str = str(path)
        if any(part.startswith('.') for part in path.parts):
            return True
        for exclude in self.exclude_paths:
            if exclude in path_str:
                return True
        return False
    
    def _get_markdown_files(self) -> List[Path]:
        """获取所有 Markdown 文件"""
        md_files = []
        for ext in ['*.md', '*.markdown', '*.MD']:
            md_files.extend(self.base_dir.rglob(ext))
        return sorted([f for f in md_files if not self._should_exclude(f)])
    
    def _check_heading_level(self, lines: List[str], file_path: str) -> List[ValidationIssue]:
        """检查标题层级连续性"""
        issues = []
        prev_level = 0
        
        for line_num, line in enumerate(lines, 1):
            match = self.HEADING_PATTERN.match(line)
            if match:
                level = len(match.group(1))
                
                # 检查是否跳过了层级
                if prev_level > 0 and level > prev_level + 1:
                    issues.append(ValidationIssue(
                        file_path=file_path,
                        line_number=line_num,
                        rule='heading-level',
                        severity='warning',
                        message=f"标题层级跳跃: H{prev_level} -> H{level}",
                        suggestion=f"考虑添加 H{prev_level + 1} 级别的标题"
                    ))
                
                # 检查标题是否为空
                title_text = match.group(2).strip()
                if not title_text:
                    issues.append(ValidationIssue(
                        file_path=file_path,
                        line_number=line_num,
                        rule='heading-level',
                        severity='error',
                        message="标题不能为空",
                        suggestion="添加标题内容"
                    ))
                
                # 严格模式：检查标题格式
                if self.strict:
                    # 检查标题后是否有标点符号
                    if title_text[-1] in '。，！？：；':
                        issues.append(ValidationIssue(
                            file_path=file_path,
                            line_number=line_num,
                            rule='heading-level',
                            severity='warning',
                            message="标题末尾不应有标点符号",
                            suggestion=f"改为: {title_text[:-1]}"
                        ))
                
                prev_level = level
        
        return issues
    
    def _check_code_block(self, lines: List[str], file_path: str) -> List[ValidationIssue]:
        """检查代码块完整性"""
        issues = []
        in_code_block = False
        code_block_start_line = 0
        code_block_lang = ""
        
        for line_num, line in enumerate(lines, 1):
            if in_code_block:
                if self.CODE_BLOCK_END.match(line):
                    in_code_block = False
            else:
                match = self.CODE_BLOCK_START.match(line)
                if match:
                    in_code_block = True
                    code_block_start_line = line_num
                    code_block_lang = match.group(1)
                    
                    # 检查代码块语言是否指定
                    if self.strict and not code_block_lang:
                        issues.append(ValidationIssue(
                            file_path=file_path,
                            line_number=line_num,
                            rule='code-block',
                            severity='info',
                            message="代码块未指定语言",
                            suggestion="添加语言标识，如 ```python"
                        ))
        
        # 检查是否有未闭合的代码块
        if in_code_block:
            issues.append(ValidationIssue(
                file_path=file_path,
                line_number=code_block_start_line,
                rule='code-block',
                severity='error',
                message="代码块未闭合",
                suggestion="在文件末尾添加 ``` 闭合代码块"
            ))
        
        return issues
    
    def _check_link_format(self, lines: List[str], file_path: str) -> List[ValidationIssue]:
        """检查链接格式"""
        issues = []
        
        for line_num, line in enumerate(lines, 1):
            # 查找所有链接
            for match in self.LINK_PATTERN.finditer(line):
                link_text = match.group(1)
                link_url = match.group(2)
                
                # 检查空链接文本
                if not link_text.strip():
                    issues.append(ValidationIssue(
                        file_path=file_path,
                        line_number=line_num,
                        rule='link-format',
                        severity='warning',
                        message="链接文本为空",
                        suggestion="添加描述性链接文本"
                    ))
                
                # 检查链接 URL
                if not link_url.strip():
                    issues.append(ValidationIssue(
                        file_path=file_path,
                        line_number=line_num,
                        rule='link-format',
                        severity='error',
                        message="链接 URL 为空",
                        suggestion="添加链接目标"
                    ))
        
        return issues
    
    def _check_image_alt(self, lines: List[str], file_path: str) -> List[ValidationIssue]:
        """检查图片 Alt 文本"""
        issues = []
        
        for line_num, line in enumerate(lines, 1):
            for match in self.IMAGE_PATTERN.finditer(line):
                alt_text = match.group(1)
                
                if not alt_text.strip():
                    issues.append(ValidationIssue(
                        file_path=file_path,
                        line_number=line_num,
                        rule='image-alt',
                        severity='warning',
                        message="图片缺少 Alt 文本",
                        suggestion="添加描述性 Alt 文本以提高可访问性"
                    ))
        
        return issues
    
    def _check_table_format(self, lines: List[str], file_path: str) -> List[ValidationIssue]:
        """检查表格格式"""
        issues = []
        in_table = False
        table_start_line = 0
        has_separator = False
        
        for line_num, line in enumerate(lines, 1):
            is_table_row = self.TABLE_ROW.match(line)
            is_separator = self.TABLE_SEPARATOR.match(line)
            
            if is_table_row or is_separator:
                if not in_table:
                    in_table = True
                    table_start_line = line_num
                    has_separator = False
                
                if is_separator:
                    has_separator = True
                
                # 检查表格行格式
                if is_table_row and '|' in line:
                    # 检查是否有空格问题
                    cells = line.split('|')[1:-1]
                    for i, cell in enumerate(cells):
                        # 检查单元格内容是否有首尾空格（除了格式需要）
                        stripped = cell.strip()
                        if cell != f' {stripped} ' and stripped:
                            pass  # 允许格式差异
            else:
                if in_table:
                    # 表格结束
                    if not has_separator and line_num - table_start_line > 1:
                        issues.append(ValidationIssue(
                            file_path=file_path,
                            line_number=table_start_line,
                            rule='table-format',
                            severity='warning',
                            message="表格缺少分隔行",
                            suggestion="在表头后添加 |---|---| 格式的分隔行"
                        ))
                    in_table = False
                    has_separator = False
        
        return issues
    
    def _check_whitespace(self, lines: List[str], file_path: str) -> List[ValidationIssue]:
        """检查空白字符"""
        issues = []
        
        for line_num, line in enumerate(lines, 1):
            # 检查行尾空格
            if self.TRAILING_WHITESPACE.search(line):
                issues.append(ValidationIssue(
                    file_path=file_path,
                    line_number=line_num,
                    rule='whitespace',
                    severity='info',
                    message="行尾有多余空格",
                    suggestion="删除行尾空格"
                ))
                self.fixable_issues.append((Path(file_path), line_num, 'trailing-whitespace', ''))
            
            # 检查空行中的空格
            if self.strict and self.WHITESPACE_LINE.match(line):
                issues.append(ValidationIssue(
                    file_path=file_path,
                    line_number=line_num,
                    rule='whitespace',
                    severity='info',
                    message="空行包含空格",
                    suggestion="删除空行中的空格"
                ))
        
        return issues
    
    def _check_line_length(self, lines: List[str], file_path: str) -> List[ValidationIssue]:
        """检查行长度"""
        issues = []
        
        for line_num, line in enumerate(lines, 1):
            # 跳过代码块中的行
            if len(line) > self.max_line_length:
                issues.append(ValidationIssue(
                    file_path=file_path,
                    line_number=line_num,
                    rule='line-length',
                    severity='warning' if self.strict else 'info',
                    message=f"行长度 ({len(line)}) 超过限制 ({self.max_line_length})",
                    suggestion="考虑换行或缩短内容"
                ))
        
        return issues
    
    def _check_front_matter(self, lines: List[str], file_path: str) -> List[ValidationIssue]:
        """检查 YAML Front Matter"""
        issues = []
        
        if not lines:
            return issues
        
        # 检查是否有 Front Matter
        if self.FRONT_MATTER_START.match(lines[0]):
            found_end = False
            for line_num, line in enumerate(lines[1:], 2):
                if self.FRONT_MATTER_START.match(line):
                    found_end = True
                    break
            
            if not found_end:
                issues.append(ValidationIssue(
                    file_path=file_path,
                    line_number=1,
                    rule='front-matter',
                    severity='error',
                    message="YAML Front Matter 未正确结束",
                    suggestion="添加结束标记 ---"
                ))
        
        return issues
    
    def _check_list_format(self, lines: List[str], file_path: str) -> List[ValidationIssue]:
        """检查列表格式"""
        issues = []
        prev_indent = -1
        
        for line_num, line in enumerate(lines, 1):
            match = self.LIST_ITEM.match(line)
            if match:
                indent = len(match.group(1))
                marker = match.group(2)
                
                # 检查缩进是否一致（通常是 2 或 4 个空格）
                if prev_indent >= 0 and indent > prev_indent:
                    if (indent - prev_indent) not in [2, 4]:
                        issues.append(ValidationIssue(
                            file_path=file_path,
                            line_number=line_num,
                            rule='list-format',
                            severity='info',
                            message="列表缩进可能不一致",
                            suggestion="使用 2 或 4 个空格缩进"
                        ))
                
                prev_indent = indent
            elif line.strip():
                prev_indent = -1
        
        return issues
    
    def validate_file(self, file_path: Path) -> FileValidationResult:
        """验证单个文件"""
        result = FileValidationResult(file_path=str(file_path.relative_to(self.base_dir)))
        
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
                lines = content.split('\n')
        except Exception as e:
            result.issues.append(ValidationIssue(
                file_path=result.file_path,
                line_number=0,
                rule='file-access',
                severity='error',
                message=f"无法读取文件: {e}",
                suggestion=None
            ))
            result.passed = False
            return result
        
        # 运行各项检查
        if 'heading-level' in self.rules:
            result.issues.extend(self._check_heading_level(lines, result.file_path))
        
        if 'code-block' in self.rules:
            result.issues.extend(self._check_code_block(lines, result.file_path))
        
        if 'link-format' in self.rules:
            result.issues.extend(self._check_link_format(lines, result.file_path))
        
        if 'table-format' in self.rules:
            result.issues.extend(self._check_table_format(lines, result.file_path))
        
        if 'front-matter' in self.rules:
            result.issues.extend(self._check_front_matter(lines, result.file_path))
        
        if 'whitespace' in self.rules:
            result.issues.extend(self._check_whitespace(lines, result.file_path))
        
        if 'line-length' in self.rules:
            result.issues.extend(self._check_line_length(lines, result.file_path))
        
        if 'list-format' in self.rules:
            result.issues.extend(self._check_list_format(lines, result.file_path))
        
        if 'image-alt' in self.rules:
            result.issues.extend(self._check_image_alt(lines, result.file_path))
        
        # 判断是否通过
        result.passed = not any(i.severity == 'error' for i in result.issues)
        if self.strict:
            result.passed = len(result.issues) == 0
        
        return result
    
    def run(self) -> ValidationReport:
        """运行验证"""
        self.report.scan_time = datetime.now().isoformat()
        self.report.base_directory = str(self.base_dir)
        self.report.rules_checked = self.rules
        
        # 获取所有 Markdown 文件
        md_files = self._get_markdown_files()
        self.report.total_files = len(md_files)
        
        # 验证每个文件
        for file_path in md_files:
            result = self.validate_file(file_path)
            self.report.results.append(result)
            
            if result.passed:
                self.report.passed_files += 1
            else:
                self.report.failed_files += 1
            
            self.report.total_issues += len(result.issues)
            
            for issue in result.issues:
                if issue.severity == 'error':
                    self.report.errors += 1
                elif issue.severity == 'warning':
                    self.report.warnings += 1
                else:
                    self.report.infos += 1
        
        return self.report
    
    def fix_issues(self):
        """自动修复一些问题"""
        fixed_count = 0
        
        # 按文件分组
        issues_by_file: Dict[Path, List[Tuple[int, str, str]]] = {}
        for file_path, line_num, issue_type, _ in self.fixable_issues:
            if file_path not in issues_by_file:
                issues_by_file[file_path] = []
            issues_by_file[file_path].append((line_num, issue_type, ''))
        
        for file_path, issues in issues_by_file.items():
            try:
                with open(file_path, 'r', encoding='utf-8') as f:
                    lines = f.readlines()
                
                modified = False
                for line_num, issue_type, _ in issues:
                    idx = line_num - 1
                    if idx < len(lines):
                        if issue_type == 'trailing-whitespace':
                            lines[idx] = lines[idx].rstrip() + '\n'
                            modified = True
                            fixed_count += 1
                
                if modified:
                    with open(file_path, 'w', encoding='utf-8') as f:
                        f.writelines(lines)
                    
            except Exception as e:
                print(f"警告: 无法修复文件 {file_path}: {e}")
        
        return fixed_count
    
    def print_report(self, verbose: bool = False):
        """打印报告"""
        print("\n" + "=" * 70)
        print("                     格式验证报告")
        print("=" * 70)
        print(f"扫描时间: {self.report.scan_time}")
        print(f"基础目录: {self.report.base_directory}")
        print(f"检查规则: {', '.join(self.report.rules_checked)}")
        print("-" * 70)
        print(f"总文件数:     {self.report.total_files}")
        print(f"通过:         {self.report.passed_files} ({self._percentage(self.report.passed_files)}%)")
        print(f"失败:         {self.report.failed_files} ({self._percentage(self.report.failed_files)}%)")
        print(f"总问题数:     {self.report.total_issues}")
        print(f"  错误:       {self.report.errors}")
        print(f"  警告:       {self.report.warnings}")
        print(f"  信息:       {self.report.infos}")
        print("=" * 70)
        
        # 打印问题详情
        failed_results = [r for r in self.report.results if not r.passed]
        if failed_results:
            print("\n❌ 发现格式问题:")
            print("-" * 70)
            
            for result in failed_results:
                print(f"\n📄 {result.file_path}")
                for issue in result.issues:
                    icon = "🔴" if issue.severity == 'error' else "🟡" if issue.severity == 'warning' else "🔵"
                    print(f"   {icon} 行 {issue.line_number} [{issue.rule}]: {issue.message}")
                    if issue.suggestion and verbose:
                        print(f"      建议: {issue.suggestion}")
        else:
            print("\n✅ 所有文件格式检查通过！")
        
        print("\n" + "=" * 70)
    
    def _percentage(self, value: int) -> float:
        """计算百分比"""
        if self.report.total_files == 0:
            return 0.0
        return round(value * 100 / self.report.total_files, 1)
    
    def save_report(self, output_path: str, format_type: str = 'text'):
        """保存报告"""
        output_path = Path(output_path)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        
        if format_type == 'json':
            self._save_json_report(output_path)
        elif format_type == 'html':
            self._save_html_report(output_path)
        else:
            self._save_text_report(output_path)
        
        print(f"\n报告已保存到: {output_path}")
    
    def _save_json_report(self, output_path: Path):
        """保存 JSON 报告"""
        report_dict = {
            'metadata': {
                'scan_time': self.report.scan_time,
                'base_directory': self.report.base_directory,
                'total_files': self.report.total_files,
                'rules_checked': self.report.rules_checked,
            },
            'summary': {
                'passed_files': self.report.passed_files,
                'failed_files': self.report.failed_files,
                'total_issues': self.report.total_issues,
                'errors': self.report.errors,
                'warnings': self.report.warnings,
                'infos': self.report.infos,
            },
            'results': [
                {
                    'file': r.file_path,
                    'passed': r.passed,
                    'issues': [asdict(i) for i in r.issues]
                }
                for r in self.report.results
            ]
        }
        
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(report_dict, f, ensure_ascii=False, indent=2)
    
    def _save_text_report(self, output_path: Path):
        """保存文本报告"""
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write("格式验证报告\n")
            f.write(f"扫描时间: {self.report.scan_time}\n")
            f.write(f"基础目录: {self.report.base_directory}\n")
            f.write("-" * 70 + "\n\n")
            
            for result in self.report.results:
                if not result.passed:
                    f.write(f"文件: {result.file_path}\n")
                    for issue in result.issues:
                        f.write(f"  行 {issue.line_number} [{issue.severity}]: {issue.message}\n")
                    f.write("\n")
    
    def _save_html_report(self, output_path: Path):
        """保存 HTML 报告"""
        html_content = f"""<!DOCTYPE html>
<html lang="zh-CN">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>格式验证报告</title>
    <style>
        body {{
            font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif;
            max-width: 1200px;
            margin: 0 auto;
            padding: 20px;
            background: #f5f5f5;
        }}
        .header {{
            background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
            color: white;
            padding: 30px;
            border-radius: 10px;
            margin-bottom: 20px;
        }}
        .stats {{
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(150px, 1fr));
            gap: 15px;
            margin-bottom: 20px;
        }}
        .stat-card {{
            background: white;
            padding: 20px;
            border-radius: 8px;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
        }}
        .stat-card.error {{ border-left: 4px solid #dc3545; }}
        .stat-card.warning {{ border-left: 4px solid #ffc107; }}
        .stat-card.success {{ border-left: 4px solid #28a745; }}
        .issue {{
            background: white;
            padding: 15px;
            margin: 10px 0;
            border-radius: 8px;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
        }}
        .issue.error {{ border-left: 4px solid #dc3545; }}
        .issue.warning {{ border-left: 4px solid #ffc107; }}
        .issue.info {{ border-left: 4px solid #17a2b8; }}
    </style>
</head>
<body>
    <div class="header">
        <h1>📝 格式验证报告</h1>
        <p>扫描时间: {self.report.scan_time}</p>
    </div>
    
    <div class="stats">
        <div class="stat-card success">
            <h3>通过</h3>
            <div class="value">{self.report.passed_files}</div>
        </div>
        <div class="stat-card error">
            <h3>失败</h3>
            <div class="value">{self.report.failed_files}</div>
        </div>
        <div class="stat-card error">
            <h3>错误</h3>
            <div class="value">{self.report.errors}</div>
        </div>
        <div class="stat-card warning">
            <h3>警告</h3>
            <div class="value">{self.report.warnings}</div>
        </div>
    </div>
"""
        
        failed_results = [r for r in self.report.results if not r.passed]
        if failed_results:
            html_content += '<div class="issues">\n<h2>发现的问题</h2>\n'
            for result in failed_results:
                for issue in result.issues:
                    html_content += f"""
        <div class="issue {issue.severity}">
            <strong>{result.file_path}</strong> - 行 {issue.line_number}<br>
            [{issue.rule}] {issue.message}
        </div>
"""
            html_content += '</div>'
        
        html_content += '</body></html>'
        
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(html_content)


def main():
    """主函数"""
    parser = argparse.ArgumentParser(
        description='验证 Markdown 文档格式',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
示例:
  %(prog)s                           # 验证当前目录
  %(prog)s -d ./docs                 # 验证指定目录
  %(prog)s --fix                     # 自动修复问题
  %(prog)s --strict                  # 严格模式
        """
    )
    
    parser.add_argument(
        '-d', '--directory',
        default='.',
        help='要验证的目录（默认: 当前目录）'
    )
    parser.add_argument(
        '-o', '--output',
        help='输出报告文件路径'
    )
    parser.add_argument(
        '-f', '--format',
        choices=['text', 'json', 'html'],
        default='text',
        help='报告格式（默认: text）'
    )
    parser.add_argument(
        '--fix',
        action='store_true',
        help='尝试自动修复一些问题'
    )
    parser.add_argument(
        '--rules',
        help='指定要检查的规则，逗号分隔'
    )
    parser.add_argument(
        '--strict',
        action='store_true',
        help='严格模式'
    )
    parser.add_argument(
        '--exclude',
        action='append',
        default=[],
        help='排除特定路径（可多次使用）'
    )
    parser.add_argument(
        '-v', '--verbose',
        action='store_true',
        help='显示详细输出'
    )
    
    args = parser.parse_args()
    
    # 解析规则
    rules = None
    if args.rules:
        rules = [r.strip() for r in args.rules.split(',')]
    
    # 检查目录
    base_dir = Path(args.directory)
    if not base_dir.exists():
        print(f"错误: 目录不存在: {base_dir}", file=sys.stderr)
        sys.exit(1)
    
    # 创建验证器
    validator = FormatValidator(
        base_dir=base_dir,
        rules=rules,
        strict=args.strict,
        exclude_paths=args.exclude
    )
    
    print(f"开始验证格式...")
    print(f"目录: {base_dir.resolve()}")
    
    # 运行验证
    report = validator.run()
    
    # 打印报告
    validator.print_report(verbose=args.verbose)
    
    # 自动修复
    if args.fix:
        print("\n正在修复问题...")
        fixed = validator.fix_issues()
        print(f"修复了 {fixed} 个问题")
    
    # 保存报告
    if args.output:
        validator.save_report(args.output, args.format)
    
    # 如果有错误，返回非零退出码
    if report.errors > 0:
        sys.exit(1)
    
    sys.exit(0)


if __name__ == '__main__':
    main()
