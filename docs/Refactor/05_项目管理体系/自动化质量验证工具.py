#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
自动化质量验证工具
用于实施形式科学重构项目的质量验证标准

作者: AI Assistant
创建时间: 2025-01-17
版本: v1.0
"""

import os
import re
import json
import time
from pathlib import Path
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass
from enum import Enum

class QualityLevel(Enum):
    """质量等级枚举"""
    EXCELLENT = "优秀"
    GOOD = "良好"
    AVERAGE = "一般"
    POOR = "较差"

@dataclass
class QualityMetric:
    """质量指标数据类"""
    name: str
    target_value: float
    current_value: float
    weight: float
    description: str

@dataclass
class VerificationResult:
    """验证结果数据类"""
    metric_name: str
    score: float
    level: QualityLevel
    issues: List[str]
    suggestions: List[str]

class QualityVerifier:
    """质量验证器"""
    
    def __init__(self, project_root: str):
        self.project_root = Path(project_root)
        self.results: List[VerificationResult] = []
        
    def verify_mathematical_formality(self, file_path: str) -> VerificationResult:
        """验证数学规范性"""
        issues = []
        suggestions = []
        score = 0.0
        
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # 检查数学定义
            math_definitions = re.findall(r'\\textbf\{定义\s+\d+\.\d+\}', content)
            if len(math_definitions) < 3:
                issues.append("数学定义数量不足")
                suggestions.append("增加严格的数学定义")
            
            # 检查数学公式
            math_formulas = re.findall(r'\$.*?\$', content)
            if len(math_formulas) < 5:
                issues.append("数学公式数量不足")
                suggestions.append("增加更多数学公式")
            
            # 检查定理证明
            theorem_proofs = re.findall(r'\\textbf\{定理\s+\d+\.\d+\}', content)
            if len(theorem_proofs) < 2:
                issues.append("定理证明数量不足")
                suggestions.append("增加定理证明")
            
            # 计算评分
            definition_score = min(len(math_definitions) / 3, 1.0) * 40
            formula_score = min(len(math_formulas) / 5, 1.0) * 30
            proof_score = min(len(theorem_proofs) / 2, 1.0) * 30
            score = definition_score + formula_score + proof_score
            
        except Exception as e:
            issues.append(f"文件读取错误: {str(e)}")
            suggestions.append("检查文件路径和编码")
        
        # 确定质量等级
        if score >= 90:
            level = QualityLevel.EXCELLENT
        elif score >= 80:
            level = QualityLevel.GOOD
        elif score >= 70:
            level = QualityLevel.AVERAGE
        else:
            level = QualityLevel.POOR
            
        return VerificationResult(
            metric_name="数学规范性",
            score=score,
            level=level,
            issues=issues,
            suggestions=suggestions
        )
    
    def verify_critical_analysis(self, file_path: str) -> VerificationResult:
        """验证批判性分析"""
        issues = []
        suggestions = []
        score = 0.0
        
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # 检查批判性分析维度
            dimensions = [
                "历史发展",
                "哲学基础", 
                "形式化",
                "应用实践",
                "跨学科"
            ]
            
            found_dimensions = []
            for dimension in dimensions:
                if dimension in content:
                    found_dimensions.append(dimension)
            
            if len(found_dimensions) < 3:
                issues.append("批判性分析维度不足")
                suggestions.append("增加更多分析维度")
            
            # 检查分析深度
            analysis_sections = re.findall(r'###\s+\d+\.\d+\s+.*?分析', content)
            if len(analysis_sections) < 2:
                issues.append("分析深度不足")
                suggestions.append("增加更深入的分析")
            
            # 检查改进建议
            suggestions_found = re.findall(r'改进建议|建议|改进', content)
            if len(suggestions_found) < 2:
                issues.append("缺乏改进建议")
                suggestions.append("增加具体的改进建议")
            
            # 计算评分
            dimension_score = min(len(found_dimensions) / 5, 1.0) * 40
            analysis_score = min(len(analysis_sections) / 2, 1.0) * 30
            suggestion_score = min(len(suggestions_found) / 2, 1.0) * 30
            score = dimension_score + analysis_score + suggestion_score
            
        except Exception as e:
            issues.append(f"文件读取错误: {str(e)}")
            suggestions.append("检查文件路径和编码")
        
        # 确定质量等级
        if score >= 90:
            level = QualityLevel.EXCELLENT
        elif score >= 80:
            level = QualityLevel.GOOD
        elif score >= 70:
            level = QualityLevel.AVERAGE
        else:
            level = QualityLevel.POOR
            
        return VerificationResult(
            metric_name="批判性分析",
            score=score,
            level=level,
            issues=issues,
            suggestions=suggestions
        )
    
    def verify_engineering_validation(self, file_path: str) -> VerificationResult:
        """验证工程验证"""
        issues = []
        suggestions = []
        score = 0.0
        
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # 检查代码实现
            code_blocks = re.findall(r'```rust.*?```', content, re.DOTALL)
            if len(code_blocks) < 1:
                issues.append("缺乏代码实现")
                suggestions.append("增加Rust代码实现")
            
            # 检查复杂度分析
            complexity_analysis = re.findall(r'时间复杂度|空间复杂度|O\(', content)
            if len(complexity_analysis) < 2:
                issues.append("复杂度分析不足")
                suggestions.append("增加详细的复杂度分析")
            
            # 检查测试用例
            test_cases = re.findall(r'测试|test|assert', content, re.IGNORECASE)
            if len(test_cases) < 1:
                issues.append("缺乏测试用例")
                suggestions.append("增加测试用例")
            
            # 计算评分
            code_score = min(len(code_blocks), 1.0) * 40
            complexity_score = min(len(complexity_analysis) / 2, 1.0) * 30
            test_score = min(len(test_cases), 1.0) * 30
            score = code_score + complexity_score + test_score
            
        except Exception as e:
            issues.append(f"文件读取错误: {str(e)}")
            suggestions.append("检查文件路径和编码")
        
        # 确定质量等级
        if score >= 90:
            level = QualityLevel.EXCELLENT
        elif score >= 80:
            level = QualityLevel.GOOD
        elif score >= 70:
            level = QualityLevel.AVERAGE
        else:
            level = QualityLevel.POOR
            
        return VerificationResult(
            metric_name="工程验证",
            score=score,
            level=level,
            issues=issues,
            suggestions=suggestions
        )
    
    def verify_file_quality(self, file_path: str) -> Dict[str, VerificationResult]:
        """验证单个文件的质量"""
        results = {}
        
        # 验证数学规范性
        results["数学规范性"] = self.verify_mathematical_formality(file_path)
        
        # 验证批判性分析
        results["批判性分析"] = self.verify_critical_analysis(file_path)
        
        # 验证工程验证
        results["工程验证"] = self.verify_engineering_validation(file_path)
        
        return results
    
    def verify_project_quality(self) -> Dict[str, any]:
        """验证整个项目的质量"""
        project_results = {
            "files_verified": 0,
            "total_score": 0.0,
            "quality_distribution": {
                QualityLevel.EXCELLENT: 0,
                QualityLevel.GOOD: 0,
                QualityLevel.AVERAGE: 0,
                QualityLevel.POOR: 0
            },
            "file_results": {},
            "overall_issues": [],
            "overall_suggestions": []
        }
        
        # 遍历项目文件
        for file_path in self.project_root.rglob("*.md"):
            if "Refactor" in str(file_path):
                continue  # 跳过Refactor目录
                
            relative_path = file_path.relative_to(self.project_root)
            print(f"验证文件: {relative_path}")
            
            try:
                file_results = self.verify_file_quality(str(file_path))
                project_results["file_results"][str(relative_path)] = file_results
                project_results["files_verified"] += 1
                
                # 计算文件平均分
                file_scores = [result.score for result in file_results.values()]
                file_avg_score = sum(file_scores) / len(file_scores)
                project_results["total_score"] += file_avg_score
                
                # 统计质量分布
                for result in file_results.values():
                    project_results["quality_distribution"][result.level] += 1
                
                # 收集问题和建议
                for result in file_results.values():
                    project_results["overall_issues"].extend(result.issues)
                    project_results["overall_suggestions"].extend(result.suggestions)
                    
            except Exception as e:
                print(f"验证文件 {relative_path} 时出错: {str(e)}")
        
        # 计算项目平均分
        if project_results["files_verified"] > 0:
            project_results["total_score"] /= project_results["files_verified"]
        
        return project_results
    
    def generate_report(self, project_results: Dict[str, any]) -> str:
        """生成验证报告"""
        report = []
        report.append("# 质量验证报告")
        report.append(f"**生成时间**: {time.strftime('%Y-%m-%d %H:%M:%S')}")
        report.append(f"**验证文件数**: {project_results['files_verified']}")
        report.append(f"**项目平均分**: {project_results['total_score']:.2f}")
        report.append("")
        
        # 质量分布
        report.append("## 质量分布")
        for level, count in project_results["quality_distribution"].items():
            percentage = (count / project_results["files_verified"]) * 100 if project_results["files_verified"] > 0 else 0
            report.append(f"- {level.value}: {count} 个文件 ({percentage:.1f}%)")
        report.append("")
        
        # 主要问题
        if project_results["overall_issues"]:
            report.append("## 主要问题")
            issue_counts = {}
            for issue in project_results["overall_issues"]:
                issue_counts[issue] = issue_counts.get(issue, 0) + 1
            
            for issue, count in sorted(issue_counts.items(), key=lambda x: x[1], reverse=True)[:10]:
                report.append(f"- {issue} (出现 {count} 次)")
            report.append("")
        
        # 改进建议
        if project_results["overall_suggestions"]:
            report.append("## 改进建议")
            suggestion_counts = {}
            for suggestion in project_results["overall_suggestions"]:
                suggestion_counts[suggestion] = suggestion_counts.get(suggestion, 0) + 1
            
            for suggestion, count in sorted(suggestion_counts.items(), key=lambda x: x[1], reverse=True)[:10]:
                report.append(f"- {suggestion} (建议 {count} 次)")
            report.append("")
        
        # 详细文件结果
        report.append("## 详细文件结果")
        for file_path, file_results in project_results["file_results"].items():
            report.append(f"### {file_path}")
            for metric_name, result in file_results.items():
                report.append(f"- {metric_name}: {result.score:.1f}分 ({result.level.value})")
                if result.issues:
                    report.append(f"  - 问题: {', '.join(result.issues[:3])}")
                if result.suggestions:
                    report.append(f"  - 建议: {', '.join(result.suggestions[:3])}")
            report.append("")
        
        return "\n".join(report)

def main():
    """主函数"""
    print("开始质量验证...")
    
    # 创建验证器
    verifier = QualityVerifier("docs")
    
    # 验证项目质量
    project_results = verifier.verify_project_quality()
    
    # 生成报告
    report = verifier.generate_report(project_results)
    
    # 保存报告
    report_path = "docs/Refactor/质量验证报告_20250117.md"
    with open(report_path, 'w', encoding='utf-8') as f:
        f.write(report)
    
    print(f"质量验证完成，报告已保存到: {report_path}")
    print(f"项目平均质量分数: {project_results['total_score']:.2f}")
    
    # 输出质量分布
    print("\n质量分布:")
    for level, count in project_results["quality_distribution"].items():
        percentage = (count / project_results["files_verified"]) * 100 if project_results["files_verified"] > 0 else 0
        print(f"- {level.value}: {count} 个文件 ({percentage:.1f}%)")

if __name__ == "__main__":
    main() 