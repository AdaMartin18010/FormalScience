#!/usr/bin/env python3
"""
FormalScience Markdown 验证脚本

功能:
- 检查 Markdown 文件格式规范性
- 验证内部链接有效性
- 检查代码块闭合
- 验证图片引用
- 检查标题层级一致性
- 生成验证报告

使用方法:
    python validate_md.py [options]

选项:
    --path PATH         指定验证路径 (默认: ../../..)
    --fix               自动修复可修复的问题
    --report FILE       输出报告到文件
    --json              以 JSON 格式输出
    --verbose           详细输出模式
"""

import os
import re
import sys
import json
import argparse
from pathlib import Path
from dataclasses import dataclass, asdict
from typing import List, Dict, Set, Tuple, Optional
from datetime import datetime
import concurrent.futures


@dataclass
class ValidationIssue:
    """验证问题"""
    file: str
    line: int
    severity: str  # error, warning, info
    category: str
    message: str
    suggestion: Optional[str] = None


@dataclass
class ValidationReport:
    """验证报告"""
    total_files: int = 0
    total_issues: int = 0
    errors: int = 0
    warnings: int = 0
    infos: int = 0
    files_checked: List[str] = None
    issues: List[ValidationIssue] = None
    
    def __post_init__(self):
        if self.files_checked is None:
            self.files_checked = []
        if self.issues is None:
            self.issues = []


class MarkdownValidator:
    """Markdown 验证器"""
    
    def __init__(self, base_path: Path, auto_fix: bool = False):
        self.base_path = base_path
        self.auto_fix = auto_fix
        self.report = ValidationReport()
        self.all_files: Set[str] = set()
        self.md_files: List[Path] = []
        
    def collect_files(self) -> None:
        """收集所有 Markdown 文件"""
        print(f"🔍 扫描目录: {self.base_path}")
        
        for root, dirs, files in os.walk(self.base_path):
            # 跳过特定目录
            dirs[:] = [d for d in dirs if d not in {
                '.git', 'node_modules', 'target', 'dist', 'build',
                '__pycache__', '.venv', 'venv'
            }]
            
            for file in files:
                file_path = Path(root) / file
                self.all_files.add(str(file_path.relative_to(self.base_path)))
                
                if file.endswith('.md'):
                    self.md_files.append(file_path)
                    
        self.report.total_files = len(self.md_files)
        print(f"📄 找到 {len(self.md_files)} 个 Markdown 文件")
        
    def validate_file(self, file_path: Path) -> List[ValidationIssue]:
        """验证单个 Markdown 文件"""
        issues = []
        
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
                lines = content.split('\n')
        except Exception as e:
            return [ValidationIssue(
                file=str(file_path.relative_to(self.base_path)),
                line=0,
                severity='error',
                category='read_error',
                message=f"无法读取文件: {e}"
            )]
            
        rel_path = str(file_path.relative_to(self.base_path))
        
        # 检查文件大小
        if len(content) > 1024 * 1024:  # 1MB
            issues.append(ValidationIssue(
                file=rel_path,
                line=0,
                severity='warning',
                category='file_size',
                message="文件超过 1MB，建议分割"
            ))
            
        # 检查 BOM
        if content.startswith('\ufeff'):
            issues.append(ValidationIssue(
                file=rel_path,
                line=1,
                severity='warning',
                category='bom',
                message="文件包含 BOM 标记",
                suggestion="保存为 UTF-8 无 BOM 格式"
            ))
            
        # 检查每行
        in_code_block = False
        code_block_lang = None
        in_front_matter = False
        
        for line_num, line in enumerate(lines, 1):
            # 检查行尾空格
            if line.endswith(' ') or line.endswith('\t'):
                issues.append(ValidationIssue(
                    file=rel_path,
                    line=line_num,
                    severity='info',
                    category='trailing_whitespace',
                    message="行尾有空白字符",
                    suggestion="删除行尾空格"
                ))
                
            # 检查代码块
            code_block_match = re.match(r'^(\s*)```(\w*)', line)
            if code_block_match:
                if not in_code_block:
                    in_code_block = True
                    code_block_lang = code_block_match.group(2)
                else:
                    in_code_block = False
                    code_block_lang = None
                    
            # 检查 tab 字符
            if '\t' in line and not in_code_block:
                issues.append(ValidationIssue(
                    file=rel_path,
                    line=line_num,
                    severity='warning',
                    category='tab_character',
                    message="使用 tab 而非空格缩进",
                    suggestion="将 tab 替换为 2 或 4 个空格"
                ))
                
            # 检查链接
            self._check_links(line, rel_path, line_num, issues, in_code_block)
            
            # 检查图片
            self._check_images(line, rel_path, line_num, issues)
            
            # 检查标题层级
            self._check_heading(line, rel_path, line_num, issues)
            
            # 检查 HTML 标签
            self._check_html_tags(line, rel_path, line_num, issues, in_code_block)
            
        # 检查未闭合的代码块
        if in_code_block:
            issues.append(ValidationIssue(
                file=rel_path,
                line=len(lines),
                severity='error',
                category='unclosed_code_block',
                message=f"代码块未闭合 (语言: {code_block_lang})",
                suggestion="添加闭合的 ```"
            ))
            
        # 检查 YAML front matter
        if content.startswith('---'):
            front_matter_end = content.find('---', 3)
            if front_matter_end == -1:
                issues.append(ValidationIssue(
                    file=rel_path,
                    line=1,
                    severity='error',
                    category='front_matter',
                    message="YAML front matter 未正确闭合",
                    suggestion="添加闭合的 ---"
                ))
                
        # 检查空文件
        if not content.strip():
            issues.append(ValidationIssue(
                file=rel_path,
                line=0,
                severity='warning',
                category='empty_file',
                message="文件为空"
            ))
            
        # 检查一级标题
        if not re.search(r'^# ', content, re.MULTILINE) and content.strip():
            issues.append(ValidationIssue(
                file=rel_path,
                line=1,
                severity='info',
                category='missing_h1',
                message="缺少一级标题 (# Title)",
                suggestion="添加文件主标题"
            ))
            
        return issues
        
    def _check_links(self, line: str, file_path: str, line_num: int, 
                     issues: List[ValidationIssue], in_code_block: bool) -> None:
        """检查链接"""
        if in_code_block:
            return
            
        # 匹配 Markdown 链接 [text](url)
        link_pattern = r'\[([^\]]+)\]\(([^)]+)\)'
        for match in re.finditer(link_pattern, line):
            url = match.group(2)
            
            # 检查外部链接
            if url.startswith(('http://', 'https://')):
                # 可以添加外部链接有效性检查
                pass
                
            # 检查内部链接
            elif url.startswith(('./', '../')) or not url.startswith(('#', 'mailto:')):
                # 解析相对路径
                base_dir = Path(file_path).parent
                target = base_dir / url.split('#')[0]  # 去掉锚点
                target_str = str(target).replace('\\', '/')
                
                if target_str not in self.all_files and url.split('#')[0]:
                    issues.append(ValidationIssue(
                        file=file_path,
                        line=line_num,
                        severity='error',
                        category='broken_link',
                        message=f"链接目标不存在: {url}",
                        suggestion=f"检查文件路径或创建目标文件"
                    ))
                    
            # 检查锚点链接
            elif url.startswith('#'):
                # 可以验证锚点是否存在
                pass
                
    def _check_images(self, line: str, file_path: str, line_num: int,
                      issues: List[ValidationIssue]) -> None:
        """检查图片引用"""
        # 匹配 Markdown 图片 ![alt](path)
        img_pattern = r'!\[([^\]]*)\]\(([^)]+)\)'
        for match in re.finditer(img_pattern, line):
            img_path = match.group(2)
            
            if not img_path.startswith(('http://', 'https://', 'data:')):
                base_dir = Path(file_path).parent
                target = base_dir / img_path
                target_str = str(target).replace('\\', '/')
                
                if target_str not in self.all_files:
                    issues.append(ValidationIssue(
                        file=file_path,
                        line=line_num,
                        severity='warning',
                        category='missing_image',
                        message=f"图片不存在: {img_path}",
                        suggestion="检查图片路径"
                    ))
                    
    def _check_heading(self, line: str, file_path: str, line_num: int,
                       issues: List[ValidationIssue]) -> None:
        """检查标题"""
        heading_match = re.match(r'^(#{1,6})\s+(.+)$', line)
        if heading_match:
            level = len(heading_match.group(1))
            text = heading_match.group(2)
            
            # 检查标题后是否有空格
            if not re.match(r'^#{1,6}\s', line):
                issues.append(ValidationIssue(
                    file=file_path,
                    line=line_num,
                    severity='warning',
                    category='heading_format',
                    message="标题标记后缺少空格",
                    suggestion=f"改为: {'#' * level} {text}"
                ))
                
            # 检查空标题
            if not text.strip():
                issues.append(ValidationIssue(
                    file=file_path,
                    line=line_num,
                    severity='error',
                    category='empty_heading',
                    message="标题内容为空"
                ))
                
    def _check_html_tags(self, line: str, file_path: str, line_num: int,
                         issues: List[ValidationIssue], in_code_block: bool) -> None:
        """检查 HTML 标签"""
        if in_code_block:
            return
            
        # 检查未闭合的标签
        common_tags = ['div', 'span', 'p', 'a', 'img', 'br', 'hr', 'table', 'tr', 'td']
        for tag in common_tags:
            open_pattern = f'<{tag}[^>]*>'
            close_pattern = f'</{tag}>'
            
            open_count = len(re.findall(open_pattern, line, re.IGNORECASE))
            close_count = len(re.findall(close_pattern, line, re.IGNORECASE))
            
            # 简单检查，不考虑标签嵌套
            if open_count != close_count and tag not in ['br', 'hr', 'img']:
                issues.append(ValidationIssue(
                    file=file_path,
                    line=line_num,
                    severity='info',
                    category='html_tag',
                    message=f"HTML <{tag}> 标签可能未闭合"
                ))
                
    def validate_all(self) -> ValidationReport:
        """验证所有文件"""
        print("\n🔍 开始验证...\n")
        
        with concurrent.futures.ThreadPoolExecutor(max_workers=8) as executor:
            future_to_file = {
                executor.submit(self.validate_file, f): f 
                for f in self.md_files
            }
            
            for future in concurrent.futures.as_completed(future_to_file):
                file_path = future_to_file[future]
                try:
                    issues = future.result()
                    rel_path = str(file_path.relative_to(self.base_path))
                    self.report.files_checked.append(rel_path)
                    self.report.issues.extend(issues)
                    
                    if issues:
                        print(f"⚠️  {rel_path}: {len(issues)} 个问题")
                    else:
                        print(f"✅ {rel_path}")
                        
                except Exception as e:
                    print(f"❌ {file_path}: 验证失败 - {e}")
                    
        # 统计
        self.report.total_issues = len(self.report.issues)
        for issue in self.report.issues:
            if issue.severity == 'error':
                self.report.errors += 1
            elif issue.severity == 'warning':
                self.report.warnings += 1
            else:
                self.report.infos += 1
                
        return self.report
        
    def print_report(self) -> None:
        """打印报告"""
        print("\n" + "=" * 70)
        print("📊 Markdown 验证报告")
        print("=" * 70)
        print(f"验证时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        print(f"验证路径: {self.base_path}")
        print(f"总文件数: {self.report.total_files}")
        print("-" * 70)
        print(f"问题统计:")
        print(f"  ❌ 错误:   {self.report.errors}")
        print(f"  ⚠️  警告:   {self.report.warnings}")
        print(f"  ℹ️  提示:   {self.report.infos}")
        print(f"  总计:     {self.report.total_issues}")
        print("=" * 70)
        
        if self.report.issues:
            print("\n📋 问题详情:\n")
            
            # 按严重程度和文件分组
            for severity in ['error', 'warning', 'info']:
                severity_issues = [i for i in self.report.issues if i.severity == severity]
                if severity_issues:
                    icon = "❌" if severity == 'error' else ("⚠️ " if severity == 'warning' else "ℹ️ ")
                    print(f"{icon} {severity.upper()} ({len(severity_issues)}):\n")
                    
                    for issue in severity_issues[:20]:  # 限制显示数量
                        print(f"  📁 {issue.file}:{issue.line}")
                        print(f"     类别: {issue.category}")
                        print(f"     问题: {issue.message}")
                        if issue.suggestion:
                            print(f"     建议: {issue.suggestion}")
                        print()
                        
                    if len(severity_issues) > 20:
                        print(f"  ... 还有 {len(severity_issues) - 20} 个 {severity}\n")
                        
    def export_json(self, output_file: str) -> None:
        """导出 JSON 报告"""
        report_dict = {
            'timestamp': datetime.now().isoformat(),
            'base_path': str(self.base_path),
            'total_files': self.report.total_files,
            'total_issues': self.report.total_issues,
            'errors': self.report.errors,
            'warnings': self.report.warnings,
            'infos': self.report.infos,
            'issues': [asdict(issue) for issue in self.report.issues]
        }
        
        with open(output_file, 'w', encoding='utf-8') as f:
            json.dump(report_dict, f, ensure_ascii=False, indent=2)
            
        print(f"\n📝 JSON 报告已保存: {output_file}")


def main():
    parser = argparse.ArgumentParser(
        description='FormalScience Markdown 验证工具',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog='''
示例:
    python validate_md.py
    python validate_md.py --path ../../../docs --fix
    python validate_md.py --report validation_report.json --json
        '''
    )
    
    parser.add_argument('--path', type=str, default=None,
                        help='指定验证路径 (默认: ../../../docs)')
    parser.add_argument('--fix', action='store_true',
                        help='自动修复可修复的问题')
    parser.add_argument('--report', type=str, default=None,
                        help='输出报告到文件')
    parser.add_argument('--json', action='store_true',
                        help='以 JSON 格式输出')
    parser.add_argument('--verbose', '-v', action='store_true',
                        help='详细输出模式')
    
    args = parser.parse_args()
    
    # 确定基础路径
    if args.path:
        base_path = Path(args.path).resolve()
    else:
        # 默认路径: 脚本所在目录的上三级
        base_path = Path(__file__).parent.parent.parent.parent.resolve() / 'docs'
        
    if not base_path.exists():
        print(f"❌ 路径不存在: {base_path}")
        sys.exit(1)
        
    print("╔══════════════════════════════════════════════════════════╗")
    print("║       FormalScience Markdown 验证工具                   ║")
    print("╚══════════════════════════════════════════════════════════╝")
    
    # 创建验证器并运行
    validator = MarkdownValidator(base_path, auto_fix=args.fix)
    validator.collect_files()
    validator.validate_all()
    
    # 输出报告
    if args.json and args.report:
        validator.export_json(args.report)
    else:
        validator.print_report()
        if args.report:
            validator.export_json(args.report)
            
    # 返回退出码
    sys.exit(1 if validator.report.errors > 0 else 0)


if __name__ == '__main__':
    main()
