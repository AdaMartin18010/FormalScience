#!/usr/bin/env python3
"""内容分析工具：分析文件内容，识别需要填充的模板占位符"""

import re
import sys
from pathlib import Path
from typing import List, Dict, Tuple

def extract_technologies(content: str) -> List[str]:
    """从文件内容中提取技术列表"""
    technologies = []
    
    # 查找章节标题中的技术名称
    pattern = r'##\s+\d+\.\d+\s+([^\n]+)'
    matches = re.findall(pattern, content)
    technologies.extend([m.strip() for m in matches])
    
    # 查找表格中的技术名称
    pattern = r'\|\s*\*\*([^*]+)\*\*\s*\|'
    matches = re.findall(pattern, content)
    technologies.extend([m.strip() for m in matches if len(m.strip()) > 3])
    
    # 去重并排序
    technologies = sorted(list(set(technologies)))
    return technologies[:10]  # 返回前10个

def extract_performance_metrics(content: str) -> Dict[str, List[float]]:
    """从文件内容中提取性能指标"""
    metrics = {}
    
    # 查找性能数据（数字+单位）
    patterns = [
        r'(\d+\.?\d*)\s*(ns|ms|μs|GHz|MHz|IPC|cycles?)',
        r'(\d+\.?\d*)\s*%',
        r'(\d+\.?\d*)\s*(条目|entries)',
    ]
    
    for pattern in patterns:
        matches = re.findall(pattern, content, re.IGNORECASE)
        for match in matches:
            if isinstance(match, tuple):
                value = float(match[0])
                unit = match[1] if len(match) > 1 else ''
                key = f"指标_{unit}"
                if key not in metrics:
                    metrics[key] = []
                metrics[key].append(value)
    
    return metrics

def extract_theory_basis(content: str) -> List[str]:
    """从文件内容中提取理论基础"""
    theories = []
    
    # 查找理论相关章节
    patterns = [
        r'##\s+\d+\s+([^#\n]+理论[^#\n]*)',
        r'###\s+\d+\.\d+\s+([^#\n]+理论[^#\n]*)',
        r'\*\*([^:]+理论)\*\*',
    ]
    
    for pattern in patterns:
        matches = re.findall(pattern, content)
        theories.extend([m.strip() for m in matches])
    
    # 去重
    theories = sorted(list(set(theories)))
    return theories[:10]

def extract_related_concepts(content: str) -> List[Tuple[str, str]]:
    """从文件内容中提取关联概念"""
    concepts = []
    
    # 查找相关主题链接
    pattern = r'\[([^\]]+)\]\(([^\)]+)\)'
    matches = re.findall(pattern, content)
    
    for name, link in matches:
        if 'md' in link.lower() or '#' in link:
            concepts.append((name.strip(), link.strip()))
    
    return concepts[:20]

def find_template_placeholders(content: str) -> Dict[str, List[str]]:
    """查找模板占位符"""
    placeholders = {
        'comparison_matrix': [],
        'theory_section': [],
        'network_section': []
    }
    
    # 查找对比矩阵占位符
    if re.search(r'特性1|特性2|技术A|技术B|方式1|方式2', content):
        placeholders['comparison_matrix'].append('对比矩阵包含占位符')
    
    # 查找理论体系占位符
    if re.search(r'调度系统基础|资源管理|性能优化\s*$', content, re.MULTILINE):
        placeholders['theory_section'].append('理论体系包含模板内容')
    
    # 查找关联网络占位符
    if re.search(r'相关文档|相关概念|基础构建', content):
        placeholders['network_section'].append('关联网络包含占位符')
    
    return placeholders

def analyze_file(file_path: Path) -> Dict:
    """分析单个文件"""
    print(f"分析文件: {file_path}")
    
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    analysis = {
        'file': str(file_path),
        'technologies': extract_technologies(content),
        'performance_metrics': extract_performance_metrics(content),
        'theory_basis': extract_theory_basis(content),
        'related_concepts': extract_related_concepts(content),
        'placeholders': find_template_placeholders(content),
        'has_substantive_content': len(extract_technologies(content)) > 0
    }
    
    return analysis

def main():
    """主函数"""
    if len(sys.argv) < 2:
        print("Usage: python content_analysis_tool.py <file_or_directory>")
        sys.exit(1)
    
    target = Path(sys.argv[1])
    
    if target.is_file():
        files = [target]
    elif target.is_dir():
        files = list(target.rglob('*.md'))
        files = [f for f in files if re.match(r'^\d+\.\d+_', f.name)]
    else:
        print(f"Error: {target} is not a valid file or directory")
        sys.exit(1)
    
    print(f"找到 {len(files)} 个文件")
    print()
    
    results = []
    for file_path in sorted(files):
        try:
            analysis = analyze_file(file_path)
            results.append(analysis)
            
            # 打印摘要
            print(f"  ✓ {file_path.name}")
            print(f"    技术: {len(analysis['technologies'])} 个")
            print(f"    性能指标: {len(analysis['performance_metrics'])} 个")
            print(f"    理论基础: {len(analysis['theory_basis'])} 个")
            print(f"    关联概念: {len(analysis['related_concepts'])} 个")
            if analysis['placeholders']:
                print(f"    ⚠️  占位符: {sum(len(v) for v in analysis['placeholders'].values())} 处")
            print()
        except Exception as e:
            print(f"  ✗ 错误: {file_path.name} - {e}")
            print()
    
    # 生成报告
    total_placeholders = sum(
        sum(len(v) for v in r['placeholders'].values())
        for r in results
    )
    total_with_content = sum(1 for r in results if r['has_substantive_content'])
    
    print("=" * 60)
    print("分析摘要")
    print("=" * 60)
    print(f"总文件数: {len(results)}")
    print(f"有实质性内容: {total_with_content} ({total_with_content/len(results)*100:.1f}%)")
    print(f"总占位符数: {total_placeholders}")
    print()
    
    # 保存详细报告
    report_file = Path('content_analysis_report.md')
    with open(report_file, 'w', encoding='utf-8') as f:
        f.write("# 内容分析报告\n\n")
        f.write(f"**分析日期**: 2025-01-27\n")
        f.write(f"**文件总数**: {len(results)}\n")
        f.write(f"**有实质性内容**: {total_with_content}\n")
        f.write(f"**总占位符数**: {total_placeholders}\n\n")
        f.write("---\n\n")
        
        for result in results:
            f.write(f"## {Path(result['file']).name}\n\n")
            f.write(f"**文件路径**: `{result['file']}`\n\n")
            
            if result['technologies']:
                f.write("### 提取的技术\n\n")
                for tech in result['technologies']:
                    f.write(f"- {tech}\n")
                f.write("\n")
            
            if result['placeholders']:
                f.write("### 占位符\n\n")
                for section, items in result['placeholders'].items():
                    if items:
                        f.write(f"**{section}**:\n")
                        for item in items:
                            f.write(f"- {item}\n")
                        f.write("\n")
            
            f.write("---\n\n")
    
    print(f"详细报告已保存到: {report_file}")

if __name__ == '__main__':
    main()
