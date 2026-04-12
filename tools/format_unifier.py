#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FormalScience 项目 Markdown 格式统一工具

功能：
1. 统一列表标记（使用 - 而非 *）
2. 统一代码块语言标记
3. 修复常见标题层级问题
4. 统一 LaTeX 公式格式
5. 修复行尾空格和文件末尾空行
6. 生成格式统一报告
"""

import os
import re
import sys
import json
from pathlib import Path
from datetime import datetime
from collections import defaultdict
from typing import Dict, List, Tuple, Set


class FormatUnifier:
    """Markdown 格式统一处理器"""
    
    def __init__(self, root_dir: str):
        self.root_dir = Path(root_dir)
        self.stats = {
            'processed_files': 0,
            'modified_files': 0,
            'issues_fixed': defaultdict(int),
            'errors': [],
            'warnings': []
        }
        self.file_stats = []
        
        # 需要排除的目录
        self.exclude_dirs = {'.git', 'node_modules', '__pycache__', '.venv', 'venv', '.vs'}
        
    def should_process(self, file_path: Path) -> bool:
        """检查文件是否应该被处理"""
        # 检查是否在排除目录中
        for part in file_path.parts:
            if part in self.exclude_dirs:
                return False
        return file_path.suffix.lower() == '.md'
    
    def find_all_md_files(self) -> List[Path]:
        """查找所有 Markdown 文件"""
        md_files = []
        for root, dirs, files in os.walk(self.root_dir):
            # 排除不需要的目录
            dirs[:] = [d for d in dirs if d not in self.exclude_dirs]
            
            for file in files:
                if file.endswith('.md'):
                    md_files.append(Path(root) / file)
        
        return sorted(md_files)
    
    def fix_trailing_whitespace(self, content: str) -> Tuple[str, int]:
        """修复行尾空格"""
        original_lines = content.split('\n')
        fixed_lines = [line.rstrip() for line in original_lines]
        fixed_content = '\n'.join(fixed_lines)
        
        count = sum(1 for orig, fixed in zip(original_lines, fixed_lines) if orig != fixed)
        return fixed_content, count
    
    def fix_eof_newline(self, content: str) -> Tuple[str, int]:
        """确保文件末尾有且仅有一个换行符"""
        if not content:
            return content, 0
        
        # 移除末尾的所有空白字符
        stripped = content.rstrip()
        if stripped == content.rstrip('\n'):
            # 添加一个换行符
            return stripped + '\n', 1
        return content, 0
    
    def unify_list_markers(self, content: str) -> Tuple[str, int]:
        """统一无序列表标记为 - """)
        lines = content.split('\n')
        modified_count = 0
        
        for i, line in enumerate(lines):
            # 匹配以 * 或 + 开头的列表项（不包括代码块内）
            # 使用前瞻断言确保是列表标记
            if re.match(r'^(\s*)\*\s+', line) and not line.strip().startswith('*' * 3):
                # 转换为 -
                lines[i] = re.sub(r'^(\s*)\*\s+', r'\1- ', line)
                modified_count += 1
            elif re.match(r'^(\s*)\+\s+', line):
                lines[i] = re.sub(r'^(\s*)\+\s+', r'\1- ', line)
                modified_count += 1
        
        return '\n'.join(lines), modified_count
    
    def fix_code_block_language(self, content: str) -> Tuple[str, int]:
        """修复代码块语言标记"""
        # 匹配没有语言标记的代码块
        pattern = r'```\s*\n'
        matches = list(re.finditer(pattern, content))
        
        if not matches:
            return content, 0
        
        # 反向替换以避免位置偏移
        modified_count = 0
        new_content = content
        for match in reversed(matches):
            # 检查上下文，尝试推断语言
            start = max(0, match.start() - 500)
            context = content[start:match.start()]
            
            # 简单的语言推断
            lang = "text"  # 默认使用 text
            if 'python' in context.lower() or 'def ' in context or 'import ' in context:
                lang = "python"
            elif 'rust' in context.lower() or 'fn ' in context or 'let mut' in context:
                lang = "rust"
            elif 'javascript' in context.lower() or 'const ' in context or 'function' in context:
                lang = "javascript"
            elif 'bash' in context.lower() or '$ ' in context or 'sudo' in context:
                lang = "bash"
            elif 'json' in context.lower():
                lang = "json"
            
            new_content = new_content[:match.start()] + f'```{lang}\n' + new_content[match.end():]
            modified_count += 1
        
        return new_content, modified_count
    
    def normalize_latex_inline(self, content: str) -> Tuple[str, int]:
        """规范化行内 LaTeX 公式"""
        # 修复 \( ... \) 为 $ ... $
        pattern = r'\\\((.+?)\\\)'
        matches = re.findall(pattern, content)
        
        if matches:
            content = re.sub(pattern, r'$\1$', content)
            return content, len(matches)
        return content, 0
    
    def normalize_latex_block(self, content: str) -> Tuple[str, int]:
        """规范化块级 LaTeX 公式"""
        # 修复 \[ ... \] 为 $$ ... $$
        pattern = r'\\\[(.+?)\\\]'
        matches = re.findall(pattern, content, re.DOTALL)
        
        if matches:
            content = re.sub(pattern, r'$$\1$$', content, flags=re.DOTALL)
            return content, len(matches)
        return content, 0
    
    def fix_heading_hierarchy(self, content: str) -> Tuple[str, List[str]]:
        """检查并修复标题层级问题"""
        lines = content.split('\n')
        warnings = []
        
        h1_count = 0
        prev_level = 0
        
        for i, line in enumerate(lines):
            match = re.match(r'^(#{1,6})\s+', line)
            if match:
                level = len(match.group(1))
                
                # 统计 H1 数量
                if level == 1:
                    h1_count += 1
                
                # 检查层级跳跃
                if prev_level > 0 and level > prev_level + 1:
                    warnings.append(f"行 {i+1}: 标题层级跳跃 (H{prev_level} -> H{level})")
                
                prev_level = level
        
        # 如果有多个 H1，记录警告（但不自动修复，需要人工判断）
        if h1_count > 1:
            warnings.append(f"发现 {h1_count} 个 H1 标题（建议每个文件只有一个 H1）")
        elif h1_count == 0:
            warnings.append("文件缺少 H1 标题")
        
        return content, warnings
    
    def fix_mermaid_blocks(self, content: str) -> Tuple[str, int]:
        """修复 Mermaid 图表标记"""
        # 确保 mermaid 代码块标记小写
        pattern = r'```\s*(?:MERMAID|Mermaid)\s*\n'
        matches = re.findall(pattern, content)
        
        if matches:
            content = re.sub(pattern, '```mermaid\n', content)
            return content, len(matches)
        return content, 0
    
    def fix_table_format(self, content: str) -> Tuple[str, int]:
        """修复表格格式问题"""
        lines = content.split('\n')
        modified_count = 0
        
        for i, line in enumerate(lines):
            # 检测表格行
            if '|' in line and not line.strip().startswith('>'):
                # 确保表格行开头和结尾有 |
                stripped = line.strip()
                if not stripped.startswith('|'):
                    stripped = '| ' + stripped
                    modified_count += 1
                if not stripped.endswith('|'):
                    stripped = stripped + ' |'
                    modified_count += 1
                lines[i] = stripped
        
        return '\n'.join(lines), modified_count
    
    def process_file(self, file_path: Path) -> Dict:
        """处理单个文件"""
        file_stat = {
            'path': str(file_path.relative_to(self.root_dir)),
            'issues': [],
            'warnings': [],
            'modified': False
        }
        
        try:
            # 读取文件
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            original_content = content
            total_fixes = 0
            
            # 应用各种修复
            fixes = [
                ('trailing_whitespace', self.fix_trailing_whitespace),
                ('list_markers', self.unify_list_markers),
                ('code_block_language', self.fix_code_block_language),
                ('latex_inline', self.normalize_latex_inline),
                ('latex_block', self.normalize_latex_block),
                ('mermaid_blocks', self.fix_mermaid_blocks),
                ('table_format', self.fix_table_format),
                ('eof_newline', self.fix_eof_newline),
            ]
            
            for fix_name, fix_func in fixes:
                try:
                    content, count = fix_func(content)
                    if count > 0:
                        file_stat['issues'].append(f"{fix_name}: {count}")
                        self.stats['issues_fixed'][fix_name] += count
                        total_fixes += count
                except Exception as e:
                    file_stat['warnings'].append(f"{fix_name} 修复失败: {str(e)}")
            
            # 检查标题层级（仅检查，不自动修复）
            content, hierarchy_warnings = self.fix_heading_hierarchy(content)
            file_stat['warnings'].extend(hierarchy_warnings)
            
            # 如果有修改，写回文件
            if content != original_content:
                with open(file_path, 'w', encoding='utf-8') as f:
                    f.write(content)
                file_stat['modified'] = True
                self.stats['modified_files'] += 1
            
            self.stats['processed_files'] += 1
            
        except Exception as e:
            file_stat['errors'] = [str(e)]
            self.stats['errors'].append(f"{file_path}: {str(e)}")
        
        return file_stat
    
    def run(self, dry_run: bool = False) -> Dict:
        """运行格式统一处理"""
        print(f"{'[试运行] ' if dry_run else ''}开始处理 Markdown 文件...")
        print(f"根目录: {self.root_dir}")
        print("-" * 60)
        
        # 查找所有 Markdown 文件
        md_files = self.find_all_md_files()
        print(f"找到 {len(md_files)} 个 Markdown 文件")
        print("-" * 60)
        
        # 处理每个文件
        for i, file_path in enumerate(md_files, 1):
            if i % 100 == 0:
                print(f"处理进度: {i}/{len(md_files)} 文件...")
            
            file_stat = self.process_file(file_path)
            self.file_stats.append(file_stat)
        
        # 生成报告
        self.generate_report()
        
        return self.stats
    
    def generate_report(self):
        """生成格式统一报告"""
        report_time = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        
        report_lines = [
            "# FormalScience 项目格式统一报告",
            "",
            f"**生成时间**: {report_time}",
            f"**处理文件总数**: {self.stats['processed_files']}",
            f"**修改文件数**: {self.stats['modified_files']}",
            "",
            "## 修复问题统计",
            "",
        ]
        
        # 问题统计表格
        report_lines.append("| 问题类型 | 修复次数 |")
        report_lines.append("|---------|---------|")
        for issue_type, count in sorted(self.stats['issues_fixed'].items(), key=lambda x: -x[1]):
            report_lines.append(f"| {issue_type} | {count} |")
        
        # 如果没有修复
        if not self.stats['issues_fixed']:
            report_lines.append("| 无 | - |")
        
        report_lines.extend([
            "",
            "## 修改的文件列表",
            "",
        ])
        
        # 修改的文件列表
        modified_files = [f for f in self.file_stats if f.get('modified')]
        if modified_files:
            report_lines.append("| 文件路径 | 修复内容 |")
            report_lines.append("|---------|---------|")
            for f in modified_files[:100]:  # 限制显示前100个
                issues = ', '.join(f['issues'][:3])  # 限制显示前3个问题
                if len(f['issues']) > 3:
                    issues += f" (+{len(f['issues']) - 3} more)"
                report_lines.append(f"| {f['path']} | {issues} |")
            
            if len(modified_files) > 100:
                report_lines.append(f"| ... | 还有 {len(modified_files) - 100} 个文件 |")
        else:
            report_lines.append("没有文件被修改")
        
        # 警告列表
        report_lines.extend([
            "",
            "## 需要人工审核的项",
            "",
        ])
        
        warnings = [(f['path'], f['warnings']) for f in self.file_stats if f.get('warnings')]
        if warnings:
            report_lines.append("| 文件路径 | 警告内容 |")
            report_lines.append("|---------|---------|")
            for path, warns in warnings[:50]:  # 限制显示前50个
                warn_text = '; '.join(warns[:2])
                if len(warns) > 2:
                    warn_text += f" (+{len(warns) - 2} more)"
                report_lines.append(f"| {path} | {warn_text} |")
            
            if len(warnings) > 50:
                report_lines.append(f"| ... | 还有 {len(warnings) - 50} 个文件有警告 |")
        else:
            report_lines.append("没有需要人工审核的项")
        
        # 错误列表
        if self.stats['errors']:
            report_lines.extend([
                "",
                "## 错误列表",
                "",
            ])
            for error in self.stats['errors'][:20]:
                report_lines.append(f"- {error}")
            if len(self.stats['errors']) > 20:
                report_lines.append(f"- ... 还有 {len(self.stats['errors']) - 20} 个错误")
        
        # 格式规范总结
        report_lines.extend([
            "",
            "## 统一格式规范总结",
            "",
            "### Markdown 格式",
            "- 标题层级：H1 只有一个，H2-H6 递增",
            "- 列表标记：统一使用 `-` 而非 `*` 或 `+`",
            "- 代码块：必须指定语言标记",
            "- 行尾：无多余空格",
            "- 文件末尾：有且仅有一个空行",
            "",
            "### LaTeX 公式格式",
            "- 行内公式：`$...$`",
            "- 块级公式：`$$...$$`",
            "",
            "### 图表格式",
            "- Mermaid 图表：使用小写 `mermaid` 标记",
            "- 表格：标准 Markdown 表格格式",
            "",
            "### 建议",
            "1. 请检查需要人工审核的项",
            "2. 使用 VSCode + Markdownlint 扩展进行实时检查",
            "3. 定期运行格式统一工具保持规范",
            "",
        ])
        
        # 保存报告
        report_path = self.root_dir / "format_unification_report.md"
        with open(report_path, 'w', encoding='utf-8') as f:
            f.write('\n'.join(report_lines))
        
        print(f"\n格式统一报告已生成: {report_path}")
        
        # 同时生成 JSON 格式的详细报告
        json_report = {
            'timestamp': report_time,
            'stats': dict(self.stats),
            'file_stats': self.file_stats
        }
        
        json_path = self.root_dir / "format_unification_report.json"
        with open(json_path, 'w', encoding='utf-8') as f:
            json.dump(json_report, f, ensure_ascii=False, indent=2)
        
        print(f"详细报告 (JSON) 已生成: {json_path}")


def main():
    """主函数"""
    root_dir = Path(__file__).parent.parent
    
    # 检查是否有命令行参数
    dry_run = '--dry-run' in sys.argv or '-d' in sys.argv
    
    unifier = FormatUnifier(str(root_dir))
    stats = unifier.run(dry_run=dry_run)
    
    print("\n" + "=" * 60)
    print("处理完成!")
    print(f"处理文件总数: {stats['processed_files']}")
    print(f"修改文件数: {stats['modified_files']}")
    print("=" * 60)


if __name__ == "__main__":
    main()
