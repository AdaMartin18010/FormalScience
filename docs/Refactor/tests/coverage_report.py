#!/usr/bin/env python3
"""
FormalScience 覆盖率报告生成器

功能:
- 统计内容覆盖率
- 分析文档完整性
- 检查代码示例覆盖
- 生成可视化 HTML 报告
- 趋势分析和对比

使用方法:
    python coverage_report.py [options]

选项:
    --output DIR        输出目录 (默认: coverage_report)
    --open              生成后自动打开报告
    --compare FILE      与历史报告对比
    --format FORMAT     输出格式: html, json, markdown (默认: html)
"""

import os
import re
import json
import argparse
from pathlib import Path
from dataclasses import dataclass, asdict
from typing import Dict, List, Set, Tuple, Optional
from datetime import datetime
from collections import defaultdict


@dataclass
class CoverageMetrics:
    """覆盖率指标"""
    total_files: int = 0
    total_lines: int = 0
    documented_files: int = 0
    code_examples: int = 0
    cross_references: int = 0
    coverage_percent: float = 0.0


@dataclass
class SectionCoverage:
    """章节覆盖率"""
    name: str
    file_count: int
    documented_count: int
    code_example_count: int
    coverage_percent: float


class CoverageAnalyzer:
    """覆盖率分析器"""
    
    # 代码块语言标识
    CODE_LANGUAGES = {
        'lean', 'rust', 'python', 'javascript', 'typescript',
        'java', 'cpp', 'c', 'go', 'haskell', 'scala', 'coq',
        'bash', 'shell', 'json', 'yaml', 'toml', 'sql'
    }
    
    def __init__(self, base_path: Path):
        self.base_path = base_path
        self.report_data = {
            'timestamp': datetime.now().isoformat(),
            'base_path': str(base_path),
            'metrics': {},
            'sections': [],
            'files': [],
            'issues': []
        }
        
    def analyze(self) -> Dict:
        """执行完整分析"""
        print("🔍 开始分析项目覆盖率...\n")
        
        # 收集所有文件
        md_files = list(self.base_path.rglob('*.md'))
        lean_files = list(self.base_path.rglob('*.lean'))
        rust_files = list(self.base_path.rglob('*.rs'))
        
        print(f"📄 Markdown 文件: {len(md_files)}")
        print(f"🔧 Lean 文件: {len(lean_files)}")
        print(f"⚙️  Rust 文件: {len(rust_files)}")
        
        # 分析 Markdown 文件
        self._analyze_markdown_files(md_files)
        
        # 分析代码文件
        self._analyze_code_files(lean_files, 'lean')
        self._analyze_code_files(rust_files, 'rust')
        
        # 计算总体指标
        self._calculate_overall_metrics()
        
        return self.report_data
        
    def _analyze_markdown_files(self, files: List[Path]) -> None:
        """分析 Markdown 文件"""
        print("\n📝 分析 Markdown 文件...")
        
        section_stats = defaultdict(lambda: {
            'files': 0, 'lines': 0, 'code_blocks': 0,
            'has_description': 0, 'has_examples': 0
        })
        
        for file_path in files:
            rel_path = str(file_path.relative_to(self.base_path))
            
            try:
                with open(file_path, 'r', encoding='utf-8') as f:
                    content = f.read()
                    lines = content.split('\n')
            except Exception as e:
                self.report_data['issues'].append({
                    'file': rel_path,
                    'error': str(e)
                })
                continue
                
            # 统计代码块
            code_blocks = re.findall(r'```(\w+)', content)
            code_count = len(code_blocks)
            code_langs = set(code_blocks)
            
            # 检查文档完整性
            has_title = bool(re.search(r'^# ', content, re.MULTILINE))
            has_description = len(content) > 500  # 粗略判断
            has_examples = code_count > 0
            
            # 章节分类
            section = self._categorize_file(rel_path)
            
            section_stats[section]['files'] += 1
            section_stats[section]['lines'] += len(lines)
            section_stats[section]['code_blocks'] += code_count
            if has_description:
                section_stats[section]['has_description'] += 1
            if has_examples:
                section_stats[section]['has_examples'] += 1
                
            # 文件详情
            self.report_data['files'].append({
                'path': rel_path,
                'section': section,
                'lines': len(lines),
                'code_blocks': code_count,
                'code_languages': list(code_langs),
                'has_title': has_title,
                'has_description': has_description,
                'has_examples': has_examples,
                'completeness_score': self._calculate_completeness(
                    has_title, has_description, has_examples, code_count
                )
            })
            
        # 章节汇总
        for section, stats in sorted(section_stats.items()):
            coverage = (stats['has_examples'] / max(stats['files'], 1)) * 100
            self.report_data['sections'].append({
                'name': section,
                'file_count': stats['files'],
                'total_lines': stats['lines'],
                'code_block_count': stats['code_blocks'],
                'documented_count': stats['has_description'],
                'example_count': stats['has_examples'],
                'coverage_percent': round(coverage, 2)
            })
            
    def _analyze_code_files(self, files: List[Path], language: str) -> None:
        """分析代码文件"""
        print(f"🔧 分析 {language} 文件...")
        
        total_lines = 0
        documented_lines = 0
        
        for file_path in files:
            try:
                with open(file_path, 'r', encoding='utf-8') as f:
                    content = f.read()
                    lines = content.split('\n')
                    total_lines += len(lines)
                    
                    # 统计注释行
                    if language == 'lean':
                        comment_lines = len([l for l in lines if l.strip().startswith('--')])
                    elif language == 'rust':
                        comment_lines = len([l for l in lines if l.strip().startswith('//')])
                    else:
                        comment_lines = 0
                        
                    documented_lines += comment_lines
            except Exception:
                continue
                
        self.report_data[f'{language}_stats'] = {
            'total_files': len(files),
            'total_lines': total_lines,
            'documented_lines': documented_lines,
            'documentation_percent': round(
                (documented_lines / max(total_lines, 1)) * 100, 2
            )
        }
        
    def _categorize_file(self, rel_path: str) -> str:
        """对文件进行分类"""
        parts = rel_path.split('/')
        
        if len(parts) >= 2:
            if 'FormalLanguage' in parts[0]:
                return '形式语言'
            elif 'FormalModel' in parts[0]:
                if 'Math' in parts[1]:
                    return '形式模型/数学'
                elif 'Software' in parts[1]:
                    return '形式模型/软件'
                elif 'AI' in parts[1]:
                    return '形式模型/AI'
                elif 'CAT' in parts[1]:
                    return '形式模型/范畴论'
                else:
                    return '形式模型/其他'
            elif 'Matter' in parts[0]:
                return '主题内容'
            elif 'Refactor' in parts[0]:
                return '重构文档'
                
        return '其他'
        
    def _calculate_completeness(self, has_title: bool, has_description: bool,
                                 has_examples: bool, code_count: int) -> float:
        """计算文档完整度分数"""
        score = 0.0
        if has_title:
            score += 20
        if has_description:
            score += 30
        if has_examples:
            score += 30
        score += min(code_count * 5, 20)  # 最多20分
        return min(score, 100)
        
    def _calculate_overall_metrics(self) -> None:
        """计算总体指标"""
        files = self.report_data['files']
        sections = self.report_data['sections']
        
        if not files:
            return
            
        total_files = len(files)
        documented = sum(1 for f in files if f['has_description'])
        with_examples = sum(1 for f in files if f['has_examples'])
        total_code_blocks = sum(f['code_blocks'] for f in files)
        avg_completeness = sum(f['completeness_score'] for f in files) / total_files
        
        self.report_data['metrics'] = {
            'total_files': total_files,
            'total_lines': sum(f['lines'] for f in files),
            'documented_files': documented,
            'files_with_examples': with_examples,
            'total_code_blocks': total_code_blocks,
            'avg_completeness_score': round(avg_completeness, 2),
            'documentation_coverage': round((documented / total_files) * 100, 2),
            'example_coverage': round((with_examples / total_files) * 100, 2),
            'section_count': len(sections)
        }
        
    def generate_html_report(self, output_dir: Path) -> Path:
        """生成 HTML 报告"""
        output_dir.mkdir(parents=True, exist_ok=True)
        
        html_content = self._generate_html_content()
        
        report_path = output_dir / 'index.html'
        with open(report_path, 'w', encoding='utf-8') as f:
            f.write(html_content)
            
        # 复制资源文件
        self._generate_css(output_dir)
        self._generate_js(output_dir)
        
        return report_path
        
    def _generate_html_content(self) -> str:
        """生成 HTML 内容"""
        metrics = self.report_data['metrics']
        sections = self.report_data['sections']
        
        # 计算进度条颜色
        def get_color(percent: float) -> str:
            if percent >= 80:
                return '#28a745'
            elif percent >= 60:
                return '#ffc107'
            else:
                return '#dc3545'
                
        html = f'''<!DOCTYPE html>
<html lang="zh-CN">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>FormalScience 覆盖率报告</title>
    <link rel="stylesheet" href="styles.css">
</head>
<body>
    <div class="container">
        <header>
            <h1>📊 FormalScience 覆盖率报告</h1>
            <p class="timestamp">生成时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}</p>
        </header>
        
        <section class="overview">
            <h2>📈 总体概览</h2>
            <div class="metrics-grid">
                <div class="metric-card">
                    <div class="metric-value">{metrics.get('total_files', 0)}</div>
                    <div class="metric-label">文档总数</div>
                </div>
                <div class="metric-card">
                    <div class="metric-value">{metrics.get('documented_files', 0)}</div>
                    <div class="metric-label">已完善文档</div>
                </div>
                <div class="metric-card">
                    <div class="metric-value">{metrics.get('files_with_examples', 0)}</div>
                    <div class="metric-label">含代码示例</div>
                </div>
                <div class="metric-card">
                    <div class="metric-value">{metrics.get('total_code_blocks', 0)}</div>
                    <div class="metric-label">代码块总数</div>
                </div>
            </div>
            
            <div class="progress-section">
                <h3>覆盖率指标</h3>
                <div class="progress-item">
                    <span class="progress-label">文档完整度</span>
                    <div class="progress-bar">
                        <div class="progress-fill" style="width: {metrics.get('documentation_coverage', 0)}%; background: {get_color(metrics.get('documentation_coverage', 0))}"></div>
                    </div>
                    <span class="progress-value">{metrics.get('documentation_coverage', 0)}%</span>
                </div>
                <div class="progress-item">
                    <span class="progress-label">代码示例覆盖</span>
                    <div class="progress-bar">
                        <div class="progress-fill" style="width: {metrics.get('example_coverage', 0)}%; background: {get_color(metrics.get('example_coverage', 0))}"></div>
                    </div>
                    <span class="progress-value">{metrics.get('example_coverage', 0)}%</span>
                </div>
                <div class="progress-item">
                    <span class="progress-label">平均完整度分数</span>
                    <div class="progress-bar">
                        <div class="progress-fill" style="width: {metrics.get('avg_completeness_score', 0)}%; background: {get_color(metrics.get('avg_completeness_score', 0))}"></div>
                    </div>
                    <span class="progress-value">{metrics.get('avg_completeness_score', 0)}分</span>
                </div>
            </div>
        </section>
        
        <section class="sections">
            <h2>📚 章节覆盖详情</h2>
            <table class="data-table">
                <thead>
                    <tr>
                        <th>章节</th>
                        <th>文件数</th>
                        <th>代码块数</th>
                        <th>覆盖率</th>
                    </tr>
                </thead>
                <tbody>
'''
        
        for section in sorted(sections, key=lambda x: x['coverage_percent'], reverse=True):
            html += f'''                    <tr>
                        <td>{section['name']}</td>
                        <td>{section['file_count']}</td>
                        <td>{section['code_block_count']}</td>
                        <td>
                            <div class="table-progress">
                                <div class="table-progress-fill" style="width: {section['coverage_percent']}%; background: {get_color(section['coverage_percent'])}"></div>
                            </div>
                            {section['coverage_percent']}%
                        </td>
                    </tr>
'''
        
        html += '''                </tbody>
            </table>
        </section>
        
        <section class="files">
            <h2>📄 文件详情</h2>
            <div class="file-list">
'''
        
        # 显示完整度较低的文档
        low_completeness = sorted(
            [f for f in self.report_data['files'] if f['completeness_score'] < 50],
            key=lambda x: x['completeness_score']
        )[:20]
        
        if low_completeness:
            html += '<h3>⚠️ 需要完善的文档 (完整度 < 50%)</h3><ul>'
            for file in low_completeness:
                html += f'<li><code>{file["path"]}</code> - 完整度: {file["completeness_score"]}%</li>'
            html += '</ul>'
            
        html += '''            </div>
        </section>
        
        <section class="languages">
            <h2>🔧 代码语言分布</h2>
            <div class="language-stats">
'''
        
        # 语言统计
        lang_stats = defaultdict(int)
        for file in self.report_data['files']:
            for lang in file.get('code_languages', []):
                if lang in self.CODE_LANGUAGES:
                    lang_stats[lang] += file['code_blocks']
                    
        for lang, count in sorted(lang_stats.items(), key=lambda x: x[1], reverse=True):
            html += f'''                <div class="language-item">
                    <span class="lang-name">{lang}</span>
                    <span class="lang-count">{count} 个代码块</span>
                </div>
'''
        
        html += '''            </div>
        </section>
        
        <footer>
            <p>Generated by FormalScience Coverage Report</p>
        </footer>
    </div>
</body>
</html>
'''
        return html
        
    def _generate_css(self, output_dir: Path) -> None:
        """生成 CSS 样式"""
        css = '''/* FormalScience Coverage Report Styles */

:root {
    --primary-color: #007bff;
    --success-color: #28a745;
    --warning-color: #ffc107;
    --danger-color: #dc3545;
    --bg-color: #f8f9fa;
    --card-bg: #ffffff;
    --text-color: #333333;
    --border-color: #dee2e6;
}

* {
    margin: 0;
    padding: 0;
    box-sizing: border-box;
}

body {
    font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;
    background: var(--bg-color);
    color: var(--text-color);
    line-height: 1.6;
}

.container {
    max-width: 1200px;
    margin: 0 auto;
    padding: 20px;
}

header {
    text-align: center;
    padding: 40px 20px;
    background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
    color: white;
    border-radius: 10px;
    margin-bottom: 30px;
}

header h1 {
    font-size: 2.5em;
    margin-bottom: 10px;
}

.timestamp {
    opacity: 0.9;
    font-size: 0.9em;
}

section {
    background: var(--card-bg);
    border-radius: 10px;
    padding: 30px;
    margin-bottom: 20px;
    box-shadow: 0 2px 10px rgba(0,0,0,0.1);
}

h2 {
    color: var(--primary-color);
    margin-bottom: 20px;
    padding-bottom: 10px;
    border-bottom: 2px solid var(--border-color);
}

.metrics-grid {
    display: grid;
    grid-template-columns: repeat(auto-fit, minmax(200px, 1fr));
    gap: 20px;
    margin-bottom: 30px;
}

.metric-card {
    background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
    color: white;
    padding: 25px;
    border-radius: 10px;
    text-align: center;
}

.metric-value {
    font-size: 3em;
    font-weight: bold;
    margin-bottom: 5px;
}

.metric-label {
    font-size: 0.9em;
    opacity: 0.9;
}

.progress-section {
    margin-top: 30px;
}

.progress-item {
    display: flex;
    align-items: center;
    margin-bottom: 20px;
    padding: 15px;
    background: var(--bg-color);
    border-radius: 8px;
}

.progress-label {
    width: 150px;
    font-weight: 500;
}

.progress-bar {
    flex: 1;
    height: 20px;
    background: #e9ecef;
    border-radius: 10px;
    overflow: hidden;
    margin: 0 15px;
}

.progress-fill {
    height: 100%;
    border-radius: 10px;
    transition: width 0.5s ease;
}

.progress-value {
    width: 80px;
    text-align: right;
    font-weight: bold;
    font-size: 1.1em;
}

.data-table {
    width: 100%;
    border-collapse: collapse;
    margin-top: 20px;
}

.data-table th,
.data-table td {
    padding: 15px;
    text-align: left;
    border-bottom: 1px solid var(--border-color);
}

.data-table th {
    background: var(--bg-color);
    font-weight: 600;
    color: var(--primary-color);
}

.data-table tr:hover {
    background: var(--bg-color);
}

.table-progress {
    width: 100px;
    height: 8px;
    background: #e9ecef;
    border-radius: 4px;
    overflow: hidden;
    display: inline-block;
    margin-right: 10px;
    vertical-align: middle;
}

.table-progress-fill {
    height: 100%;
    border-radius: 4px;
}

.file-list h3 {
    color: var(--danger-color);
    margin-bottom: 15px;
}

.file-list ul {
    list-style: none;
}

.file-list li {
    padding: 8px 12px;
    background: var(--bg-color);
    margin-bottom: 5px;
    border-radius: 5px;
    border-left: 3px solid var(--warning-color);
}

.file-list code {
    font-family: 'Consolas', 'Monaco', monospace;
    font-size: 0.9em;
    color: var(--primary-color);
}

.language-stats {
    display: grid;
    grid-template-columns: repeat(auto-fit, minmax(200px, 1fr));
    gap: 15px;
    margin-top: 20px;
}

.language-item {
    display: flex;
    justify-content: space-between;
    padding: 15px 20px;
    background: var(--bg-color);
    border-radius: 8px;
    border-left: 4px solid var(--primary-color);
}

.lang-name {
    font-weight: 600;
    text-transform: uppercase;
}

.lang-count {
    color: #666;
}

footer {
    text-align: center;
    padding: 20px;
    color: #666;
    font-size: 0.9em;
}

@media (max-width: 768px) {
    .metrics-grid {
        grid-template-columns: repeat(2, 1fr);
    }
    
    .progress-item {
        flex-direction: column;
        align-items: flex-start;
    }
    
    .progress-label {
        width: 100%;
        margin-bottom: 10px;
    }
    
    .progress-bar {
        width: 100%;
        margin: 10px 0;
    }
}
'''
        with open(output_dir / 'styles.css', 'w') as f:
            f.write(css)
            
    def _generate_js(self, output_dir: Path) -> None:
        """生成 JavaScript 文件"""
        js = '''// FormalScience Coverage Report Scripts

document.addEventListener('DOMContentLoaded', function() {
    // 添加动画效果
    const progressFills = document.querySelectorAll('.progress-fill');
    
    progressFills.forEach(fill => {
        const width = fill.style.width;
        fill.style.width = '0%';
        setTimeout(() => {
            fill.style.width = width;
        }, 100);
    });
    
    // 表格排序功能
    const tables = document.querySelectorAll('.data-table');
    tables.forEach(table => {
        const headers = table.querySelectorAll('th');
        headers.forEach((header, index) => {
            header.style.cursor = 'pointer';
            header.addEventListener('click', () => {
                sortTable(table, index);
            });
        });
    });
});

function sortTable(table, column) {
    const tbody = table.querySelector('tbody');
    const rows = Array.from(tbody.querySelectorAll('tr'));
    
    rows.sort((a, b) => {
        const aVal = a.cells[column].textContent.trim();
        const bVal = b.cells[column].textContent.trim();
        
        // 尝试数值排序
        const aNum = parseFloat(aVal);
        const bNum = parseFloat(bVal);
        
        if (!isNaN(aNum) && !isNaN(bNum)) {
            return bNum - aNum;
        }
        
        return aVal.localeCompare(bVal);
    });
    
    rows.forEach(row => tbody.appendChild(row));
}
'''
        with open(output_dir / 'scripts.js', 'w') as f:
            f.write(js)
            
    def export_json(self, output_path: Path) -> None:
        """导出 JSON 报告"""
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(self.report_data, f, ensure_ascii=False, indent=2)


def main():
    parser = argparse.ArgumentParser(
        description='FormalScience 覆盖率报告生成器',
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    
    parser.add_argument('--output', type=str, default='coverage_report',
                        help='输出目录 (默认: coverage_report)')
    parser.add_argument('--open', action='store_true',
                        help='生成后自动打开报告')
    parser.add_argument('--format', type=str, default='html',
                        choices=['html', 'json', 'markdown'],
                        help='输出格式 (默认: html)')
    
    args = parser.parse_args()
    
    # 确定基础路径
    base_path = Path(__file__).parent.parent.parent.parent.resolve() / 'docs'
    
    if not base_path.exists():
        print(f"❌ 路径不存在: {base_path}")
        return
        
    print("╔══════════════════════════════════════════════════════════╗")
    print("║       FormalScience 覆盖率报告生成器                    ║")
    print("╚══════════════════════════════════════════════════════════╝\n")
    
    # 创建分析器
    analyzer = CoverageAnalyzer(base_path)
    analyzer.analyze()
    
    # 生成报告
    output_dir = Path(args.output)
    
    if args.format == 'html':
        report_path = analyzer.generate_html_report(output_dir)
        print(f"\n✅ HTML 报告已生成: {report_path}")
        
        # 同时导出 JSON
        json_path = output_dir / 'report.json'
        analyzer.export_json(json_path)
        print(f"✅ JSON 数据已导出: {json_path}")
        
        if args.open:
            import webbrowser
            webbrowser.open(f'file://{report_path.absolute()}')
            
    elif args.format == 'json':
        json_path = output_dir / 'report.json'
        analyzer.export_json(json_path)
        print(f"\n✅ JSON 报告已生成: {json_path}")
        
    elif args.format == 'markdown':
        md_path = output_dir / 'report.md'
        # 生成 Markdown 报告
        with open(md_path, 'w', encoding='utf-8') as f:
            f.write(f"# FormalScience 覆盖率报告\n\n")
            f.write(f"生成时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n\n")
            
            metrics = analyzer.report_data['metrics']
            f.write("## 总体指标\n\n")
            f.write(f"- 文档总数: {metrics.get('total_files', 0)}\n")
            f.write(f"- 已完善文档: {metrics.get('documented_files', 0)}\n")
            f.write(f"- 代码示例覆盖: {metrics.get('example_coverage', 0)}%\n")
            f.write(f"- 平均完整度: {metrics.get('avg_completeness_score', 0)}分\n\n")
            
            f.write("## 章节覆盖\n\n")
            f.write("| 章节 | 文件数 | 覆盖率 |\n")
            f.write("|------|--------|--------|\n")
            for section in analyzer.report_data['sections']:
                f.write(f"| {section['name']} | {section['file_count']} | {section['coverage_percent']}% |\n")
                
        print(f"\n✅ Markdown 报告已生成: {md_path}")


if __name__ == '__main__':
    main()
