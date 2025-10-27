#!/usr/bin/env python3
"""
文档结构检查和修复工具
检查所有Perspective下文档的结构一致性
"""

import os
import re
from pathlib import Path
from typing import Dict, List, Tuple
import sys

class DocumentChecker:
    def __init__(self, base_path: str):
        self.base_path = Path(base_path)
        self.issues = []
        
    def check_file(self, filepath: Path) -> Dict:
        """检查单个文件的结构"""
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
        
        issues = {}
        lines = content.split('\n')
        
        # 检查标题（第一行）
        if lines:
            first_line = lines[0].strip()
            if first_line.startswith('#'):
                # 检查是否有序号
                # 匹配模式：# 1.1 标题 或 # 01 标题
                has_number = bool(re.match(r'^#\s+(\d+\.?\d*)\s+', first_line))
                issues['has_numbered_title'] = has_number
                issues['title'] = first_line
            else:
                issues['has_numbered_title'] = False
                issues['title'] = None
        
        # 检查元数据块
        metadata_pattern = r'>\s\*\*文档版本\*\*:'
        has_metadata = bool(re.search(metadata_pattern, content))
        issues['has_metadata'] = has_metadata
        
        # 检查目录
        toc_patterns = [
            r'##\s+目录',
            r'##\s+Table of Contents',
            r'##\s+目录\s+\|\s+Table of Contents'
        ]
        has_toc = any(re.search(pattern, content) for pattern in toc_patterns)
        issues['has_toc'] = has_toc
        
        # 检查核心概念深度分析
        deep_analysis_pattern = r'##\s+📊\s+核心概念深度分析'
        has_deep_analysis = bool(re.search(deep_analysis_pattern, content))
        issues['has_deep_analysis'] = has_deep_analysis
        
        # 检查导航
        navigation_patterns = [
            r'\*\*导航\*\*：',
            r'Navigation:',
            r'\[← 上一节',
            r'\[下一节 →\]'
        ]
        has_navigation = any(re.search(pattern, content) for pattern in navigation_patterns)
        issues['has_navigation'] = has_navigation
        
        # 检查相关主题
        related_topics_pattern = r'##\s+相关主题'
        has_related_topics = bool(re.search(related_topics_pattern, content))
        issues['has_related_topics'] = has_related_topics
        
        issues['line_count'] = len(lines)
        
        return issues
    
    def scan_perspective(self, perspective_name: str) -> List[Dict]:
        """扫描一个Perspective下的所有文件"""
        perspective_path = self.base_path / perspective_name
        if not perspective_path.exists():
            print(f"⚠️  路径不存在: {perspective_path}")
            return []
        
        results = []
        for md_file in perspective_path.rglob("*.md"):
            # 跳过README、FAQ等特殊文件
            if md_file.name in ['README.md', 'FAQ.md', 'GLOSSARY.md', 
                                'QUICK_REFERENCE.md', 'LEARNING_PATHS.md',
                                '00_Master_Index.md', 'COMPLETION_SUMMARY.md',
                                'CONCEPT_ALIGNMENT_TABLE.md']:
                continue
            
            issues = self.check_file(md_file)
            issues['filepath'] = md_file.relative_to(self.base_path)
            issues['filename'] = md_file.name
            results.append(issues)
        
        return results
    
    def generate_report(self, perspective_name: str, results: List[Dict]) -> str:
        """生成报告"""
        report = [f"\n{'='*80}"]
        report.append(f"{perspective_name} 结构检查报告")
        report.append(f"{'='*80}\n")
        
        total_files = len(results)
        
        # 统计各项指标
        stats = {
            'has_numbered_title': 0,
            'has_metadata': 0,
            'has_toc': 0,
            'has_deep_analysis': 0,
            'has_navigation': 0,
            'has_related_topics': 0
        }
        
        missing_toc_files = []
        missing_number_files = []
        missing_nav_files = []
        
        for result in results:
            for key in stats:
                if result.get(key, False):
                    stats[key] += 1
            
            if not result.get('has_toc', False):
                missing_toc_files.append(result['filepath'])
            if not result.get('has_numbered_title', False):
                missing_number_files.append(result['filepath'])
            if not result.get('has_navigation', False):
                missing_nav_files.append(result['filepath'])
        
        # 生成统计信息
        report.append(f"总文件数: {total_files}")
        report.append(f"\n结构元素覆盖率:")
        report.append(f"  ✓ 标题有序号:     {stats['has_numbered_title']:3d}/{total_files} ({stats['has_numbered_title']*100//total_files}%)")
        report.append(f"  ✓ 有元数据块:     {stats['has_metadata']:3d}/{total_files} ({stats['has_metadata']*100//total_files}%)")
        report.append(f"  ✓ 有目录:         {stats['has_toc']:3d}/{total_files} ({stats['has_toc']*100//total_files}%)")
        report.append(f"  ✓ 有深度分析:     {stats['has_deep_analysis']:3d}/{total_files} ({stats['has_deep_analysis']*100//total_files}%)")
        report.append(f"  ✓ 有导航:         {stats['has_navigation']:3d}/{total_files} ({stats['has_navigation']*100//total_files}%)")
        report.append(f"  ✓ 有相关主题:     {stats['has_related_topics']:3d}/{total_files} ({stats['has_related_topics']*100//total_files}%)")
        
        # 列出需要修复的文件
        if missing_toc_files:
            report.append(f"\n❌ 缺少目录的文件 ({len(missing_toc_files)}个):")
            for filepath in missing_toc_files[:10]:  # 只显示前10个
                report.append(f"   - {filepath}")
            if len(missing_toc_files) > 10:
                report.append(f"   ... 还有 {len(missing_toc_files) - 10} 个文件")
        
        if missing_number_files:
            report.append(f"\n❌ 标题无序号的文件 ({len(missing_number_files)}个):")
            for filepath in missing_number_files[:10]:
                report.append(f"   - {filepath}")
            if len(missing_number_files) > 10:
                report.append(f"   ... 还有 {len(missing_number_files) - 10} 个文件")
        
        if missing_nav_files:
            report.append(f"\n❌ 缺少导航的文件 ({len(missing_nav_files)}个):")
            for filepath in missing_nav_files[:10]:
                report.append(f"   - {filepath}")
            if len(missing_nav_files) > 10:
                report.append(f"   ... 还有 {len(missing_nav_files) - 10} 个文件")
        
        return "\n".join(report)

def main():
    base_path = Path(__file__).parent.parent / "Concept"
    
    if len(sys.argv) > 1:
        base_path = Path(sys.argv[1])
    
    print(f"🔍 扫描路径: {base_path}")
    
    checker = DocumentChecker(base_path)
    
    perspectives = [
        "Software_Perspective",
        "AI_model_Perspective",
        "FormalLanguage_Perspective",
        "Information_Theory_Perspective"
    ]
    
    all_reports = []
    all_results = {}
    
    for perspective in perspectives:
        print(f"\n📊 正在扫描 {perspective}...")
        results = checker.scan_perspective(perspective)
        all_results[perspective] = results
        report = checker.generate_report(perspective, results)
        all_reports.append(report)
        print(report)
    
    # 生成总结报告
    print(f"\n{'='*80}")
    print("总体统计")
    print(f"{'='*80}\n")
    
    total_files = sum(len(results) for results in all_results.values())
    print(f"总文件数: {total_files}")
    
    for perspective, results in all_results.items():
        print(f"  {perspective}: {len(results)} 个文件")
    
    # 保存报告到文件
    report_file = base_path / "STRUCTURE_CHECK_REPORT.md"
    with open(report_file, 'w', encoding='utf-8') as f:
        f.write("# 文档结构检查报告\n\n")
        f.write(f"> 生成时间: 2025-10-27\n\n")
        for report in all_reports:
            f.write(report)
            f.write("\n\n")
    
    print(f"\n✅ 报告已保存到: {report_file}")

if __name__ == "__main__":
    main()

