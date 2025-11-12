#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
删除重复的目录部分，只保留第一个目录
"""

import os
import re
from pathlib import Path

def remove_duplicate_toc(filepath):
    """删除文件中的重复目录"""
    print(f"处理文件: {filepath}")
    
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            lines = f.readlines()
    except Exception as e:
        print(f"  错误：无法读取文件 - {e}")
        return False
    
    toc_positions = []
    for i, line in enumerate(lines):
        if '## 📋 目录' in line or '## 目录' in line or '## 目录 | Table of Contents' in line:
            toc_positions.append(i)
    
    if len(toc_positions) <= 1:
        print(f"  跳过：只有一个或没有目录")
        return False
    
    # 找到每个目录的结束位置
    toc_ranges = []
    for start in toc_positions:
        end = start
        for i in range(start + 1, len(lines)):
            if lines[i].strip() == '---' and i > start + 2:
                end = i
                break
        toc_ranges.append((start, end))
    
    # 保留第一个目录，删除其他目录
    new_lines = []
    skip_ranges = toc_ranges[1:]  # 跳过除第一个外的所有目录
    
    i = 0
    while i < len(lines):
        should_skip = False
        for start, end in skip_ranges:
            if start <= i <= end:
                should_skip = True
                break
        
        if should_skip:
            # 跳过这个范围
            for start, end in skip_ranges:
                if start <= i <= end:
                    i = end + 1
                    break
        else:
            new_lines.append(lines[i])
            i += 1
    
    # 写回文件
    try:
        with open(filepath, 'w', encoding='utf-8') as f:
            f.writelines(new_lines)
        print(f"  完成：已删除 {len(skip_ranges)} 个重复目录")
        return True
    except Exception as e:
        print(f"  错误：无法写入文件 - {e}")
        return False

def main():
    """主函数"""
    base_dir = Path(__file__).parent
    
    # 指定要处理的文件
    target_files = [
        'Concept/AI_model_Perspective/02_Neural_Network_Theory/02.2_RNN_Transformer_Architecture.md',
        'Concept/AI_model_Perspective/02_Neural_Network_Theory/02.4_Transformer_Architecture.md',
        'Concept/AI_model_Perspective/02_Neural_Network_Theory/02.5_Universal_Approximation_Theorem.md',
        'Concept/AI_model_Perspective/03_Language_Models/03.4_Token_Generation_Mechanisms.md',
        'Concept/AI_model_Perspective/03_Language_Models/03.5_Embedding_Vector_Spaces.md',
        'Concept/AI_model_Perspective/03_Language_Models/03.6_Context_Window_Memory.md',
        'Concept/AI_model_Perspective/04_Semantic_Models/04.2_Continuous_Representation_Theory.md',
        'Concept/AI_model_Perspective/04_Semantic_Models/04.3_Distributional_Semantics.md',
        'Concept/AI_model_Perspective/04_Semantic_Models/04.4_Semantic_Similarity_Metrics.md',
        'Concept/AI_model_Perspective/04_Semantic_Models/04.5_Multimodal_Semantic_Integration.md',
        'Concept/AI_model_Perspective/04_Semantic_Models/04.6_Huang_Semantic_Model_Analysis.md',
        'Concept/AI_model_Perspective/05_Learning_Theory/05.2_Gold_Learnability_Theory.md',
    ]
    
    print(f"找到 {len(target_files)} 个文件需要处理")
    print("")
    
    processed = 0
    skipped = 0
    errors = 0
    
    for file_path in target_files:
        filepath = base_dir / file_path
        if not filepath.exists():
            print(f"  跳过：文件不存在 - {filepath}")
            skipped += 1
            continue
        
        try:
            if remove_duplicate_toc(filepath):
                processed += 1
            else:
                skipped += 1
        except Exception as e:
            print(f"  错误：处理文件时出错 - {e}")
            errors += 1
    
    print(f"\n{'='*60}")
    print(f"处理完成：")
    print(f"  - 成功处理：{processed} 个文件")
    print(f"  - 跳过：{skipped} 个文件")
    print(f"  - 错误：{errors} 个文件")
    print(f"{'='*60}")

if __name__ == '__main__':
    main()
