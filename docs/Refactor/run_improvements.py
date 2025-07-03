#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
形式科学项目改进执行脚本
用于自动化执行所有改进工作

用法:
    python run_improvements.py [--phase PHASE] [--module MODULE]

参数:
    --phase     执行阶段（1-4）
                1: 目录结构规范化
                2: 断链修复
                3: 内容补充
                4: 质量检查
    --module    要处理的模块（如01_Philosophical_Foundations）
"""

import os
import sys
import argparse
import subprocess
import datetime
import shutil
from pathlib import Path

# 项目根目录
ROOT_DIR = Path(os.path.dirname(os.path.abspath(__file__))).parent.parent

# 模块列表
MODULES = [
    "01_Philosophical_Foundations",
    "02_Mathematical_Foundations",
    "03_Logic_Theory",
    "04_Formal_Language_Theory",
    "05_Type_Theory",
    "06_Formal_Model_Theory",
    "07_Programming_Language_Theory",
    "08_Software_Engineering_Theory",
    "09_Computer_Architecture_Theory",
    "10_Distributed_Systems_Theory",
    "11_Computer_Network_Theory",
    "12_Database_Theory",
    "13_Artificial_Intelligence_Theory",
    "14_Algorithm_Theory",
    "15_Information_Theory",
    "16_Cross_Domain_Synthesis"
]

def run_command(command, cwd=None):
    """运行命令并返回输出"""
    try:
        result = subprocess.run(
            command,
            cwd=cwd or ROOT_DIR,
            shell=True,
            check=True,
            capture_output=True,
            text=True
        )
        return result.stdout
    except subprocess.CalledProcessError as e:
        print(f"命令执行失败: {e}")
        print(f"错误输出: {e.stderr}")
        return None

def backup_directory(directory):
    """备份目录"""
    timestamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
    backup_dir = f"{directory}_backup_{timestamp}"
    try:
        shutil.copytree(directory, backup_dir)
        print(f"已备份目录 {directory} 到 {backup_dir}")
        return True
    except Exception as e:
        print(f"备份目录失败: {e}")
        return False

def phase1_directory_normalization(module=None):
    """阶段1: 目录结构规范化"""
    print("\n=== 执行阶段1: 目录结构规范化 ===\n")
    
    # 备份目录
    if module:
        target_dir = os.path.join(ROOT_DIR, "docs", "Refactor", module)
        if os.path.exists(target_dir):
            backup_directory(target_dir)
    else:
        backup_directory(os.path.join(ROOT_DIR, "docs", "Refactor"))
    
    # 执行目录规范化脚本
    # 注意: 这里假设已经有了目录规范化脚本，实际使用时需要创建或调整
    normalization_script = os.path.join(ROOT_DIR, "docs", "Refactor", "directory_normalizer.py")
    if os.path.exists(normalization_script):
        cmd = f"python {normalization_script}"
        if module:
            cmd += f" --module {module}"
        print(f"执行命令: {cmd}")
        output = run_command(cmd)
        if output:
            print(output)
    else:
        print(f"警告: 找不到目录规范化脚本 {normalization_script}")
        print("手动执行目录规范化步骤:")
        print("1. 按照目录编号规范化执行方案_20250117.md中的规则重命名目录")
        print("2. 确保目录结构符合规范")
        print("3. 更新相关README文件中的目录结构描述")

def phase2_link_fixing(module=None):
    """阶段2: 断链修复"""
    print("\n=== 执行阶段2: 断链修复 ===\n")
    
    # 运行链接修复工具
    link_fixer = os.path.join(ROOT_DIR, "docs", "Refactor", "link_fixer.py")
    if os.path.exists(link_fixer):
        target_dir = os.path.join(ROOT_DIR, "docs", "Refactor")
        if module:
            target_dir = os.path.join(target_dir, module)
        
        # 先检查断链
        cmd = f"python {link_fixer} --report {target_dir}"
        print(f"执行命令: {cmd}")
        output = run_command(cmd)
        if output:
            print(output)
        
        # 询问是否修复
        answer = input("是否执行断链修复? (y/n): ")
        if answer.lower() == 'y':
            cmd = f"python {link_fixer} --fix {target_dir}"
            print(f"执行命令: {cmd}")
            output = run_command(cmd)
            if output:
                print(output)
    else:
        print(f"警告: 找不到链接修复工具 {link_fixer}")

def phase3_content_enhancement(module=None):
    """阶段3: 内容补充"""
    print("\n=== 执行阶段3: 内容补充 ===\n")
    
    # 运行批判性分析补充工具
    analysis_tool = os.path.join(ROOT_DIR, "docs", "Refactor", "批判性分析补充工具.py")
    if os.path.exists(analysis_tool):
        target_dir = os.path.join(ROOT_DIR, "docs", "Refactor")
        if module:
            target_dir = os.path.join(target_dir, module)
        
        # 先检查缺失的批判性分析
        cmd = f"python {analysis_tool} --check {target_dir}"
        print(f"执行命令: {cmd}")
        output = run_command(cmd)
        if output:
            print(output)
        
        # 询问是否应用模板
        answer = input("是否应用批判性分析模板? (y/n): ")
        if answer.lower() == 'y':
            cmd = f"python {analysis_tool} --apply {target_dir}"
            print(f"执行命令: {cmd}")
            output = run_command(cmd)
            if output:
                print(output)
    else:
        print(f"警告: 找不到批判性分析补充工具 {analysis_tool}")

def phase4_quality_check(module=None):
    """阶段4: 质量检查"""
    print("\n=== 执行阶段4: 质量检查 ===\n")
    
    # 检查断链
    link_fixer = os.path.join(ROOT_DIR, "docs", "Refactor", "link_fixer.py")
    if os.path.exists(link_fixer):
        target_dir = os.path.join(ROOT_DIR, "docs", "Refactor")
        if module:
            target_dir = os.path.join(target_dir, module)
        
        cmd = f"python {link_fixer} --report {target_dir}"
        print(f"执行命令: {cmd}")
        output = run_command(cmd)
        if output:
            print(output)
    
    # 检查批判性分析覆盖率
    analysis_tool = os.path.join(ROOT_DIR, "docs", "Refactor", "批判性分析补充工具.py")
    if os.path.exists(analysis_tool):
        target_dir = os.path.join(ROOT_DIR, "docs", "Refactor")
        if module:
            target_dir = os.path.join(target_dir, module)
        
        cmd = f"python {analysis_tool} --check {target_dir}"
        print(f"执行命令: {cmd}")
        output = run_command(cmd)
        if output:
            print(output)
    
    # 更新进度报告
    print("\n正在生成质量检查报告...")
    timestamp = datetime.datetime.now().strftime("%Y%m%d")
    report_file = os.path.join(ROOT_DIR, "docs", "Refactor", f"质量检查报告_{timestamp}.md")
    
    with open(report_file, 'w', encoding='utf-8') as f:
        f.write(f"# 形式科学项目质量检查报告\n\n")
        f.write(f"**生成时间**: {datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n\n")
        
        f.write("## 1. 断链检查\n\n")
        f.write("请参考link_fix_report.txt获取详细的断链信息。\n\n")
        
        f.write("## 2. 批判性分析覆盖率\n\n")
        f.write("请运行批判性分析补充工具.py --check获取详细的覆盖率信息。\n\n")
        
        f.write("## 3. 建议\n\n")
        f.write("1. 优先修复高优先级文档中的断链\n")
        f.write("2. 补充核心概念文档中缺失的批判性分析\n")
        f.write("3. 为所有文档增加历史维度和实践应用内容\n")
        f.write("4. 提高形式化表达程度\n")
        f.write("5. 加强跨学科整合\n\n")
        
        f.write("## 4. 下一步计划\n\n")
        f.write("请参考改进进度跟踪_20250117.md获取详细的计划信息。\n")
    
    print(f"质量检查报告已生成: {report_file}")

def main():
    parser = argparse.ArgumentParser(description='形式科学项目改进执行脚本')
    parser.add_argument('--phase', type=int, choices=[1, 2, 3, 4], help='执行阶段')
    parser.add_argument('--module', help='要处理的模块')
    
    args = parser.parse_args()
    
    # 验证模块名称
    if args.module and args.module not in MODULES:
        print(f"错误: 无效的模块名称 '{args.module}'")
        print(f"有效的模块名称: {', '.join(MODULES)}")
        return
    
    # 如果没有指定阶段，则显示菜单
    if args.phase is None:
        while True:
            print("\n=== 形式科学项目改进执行脚本 ===\n")
            print("请选择要执行的阶段:")
            print("1. 目录结构规范化")
            print("2. 断链修复")
            print("3. 内容补充")
            print("4. 质量检查")
            print("0. 退出")
            
            choice = input("\n请输入选择 (0-4): ")
            
            if choice == '0':
                break
            elif choice in ['1', '2', '3', '4']:
                phase = int(choice)
                
                # 询问是否指定模块
                if not args.module:
                    print("\n请选择要处理的模块:")
                    print("0. 所有模块")
                    for i, module in enumerate(MODULES, 1):
                        print(f"{i}. {module}")
                    
                    module_choice = input("\n请输入选择 (0-%d): " % len(MODULES))
                    
                    if module_choice == '0':
                        module = None
                    elif module_choice.isdigit() and 1 <= int(module_choice) <= len(MODULES):
                        module = MODULES[int(module_choice) - 1]
                    else:
                        print("无效的选择，将处理所有模块")
                        module = None
                else:
                    module = args.module
                
                # 执行选择的阶段
                if phase == 1:
                    phase1_directory_normalization(module)
                elif phase == 2:
                    phase2_link_fixing(module)
                elif phase == 3:
                    phase3_content_enhancement(module)
                elif phase == 4:
                    phase4_quality_check(module)
            else:
                print("无效的选择，请重试")
    else:
        # 直接执行指定阶段
        if args.phase == 1:
            phase1_directory_normalization(args.module)
        elif args.phase == 2:
            phase2_link_fixing(args.module)
        elif args.phase == 3:
            phase3_content_enhancement(args.module)
        elif args.phase == 4:
            phase4_quality_check(args.module)

if __name__ == '__main__':
    main() 