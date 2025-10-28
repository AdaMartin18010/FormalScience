#!/usr/bin/env python3
"""
批量修复重复目录问题
删除文件中的简略版"## 目录 | Table of Contents"目录
"""
import re
import sys
from pathlib import Path

def fix_duplicate_toc(file_path):
    """修复单个文件的重复目录"""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # 检测是否有重复目录
        if content.count('## 目录') < 2:
            print(f"⏭️  跳过: {file_path.name} (无重复目录)")
            return False
        
        # 模式1: 删除"## 目录 | Table of Contents"开头到"---"之间的简略目录
        # 保留后面的详细"## 目录"
        pattern1 = r'---\s*\n\s*## 目录 \| Table of Contents\s*\n.*?---\s*\n\s*## 目录'
        if re.search(pattern1, content, re.DOTALL):
            content_new = re.sub(pattern1, '---\n\n## 目录', content, flags=re.DOTALL)
            with open(file_path, 'w', encoding='utf-8') as f:
                f.write(content_new)
            print(f"✅ 修复: {file_path.name}")
            return True
        
        print(f"⚠️  未识别: {file_path.name} (模式不匹配)")
        return False
        
    except Exception as e:
        print(f"❌ 错误: {file_path.name} - {str(e)}")
        return False

def main():
    base_dir = Path(__file__).parent.parent / "Concept" / "Information_Theory_Perspective"
    
    # 需要修复的章节和文件
    chapters = {
        "03_DIKWP_Model": ["03.2_Semantic_Information_Theory.md", "03.3_Formal_Verification.md", "03.4_Computational_Implementation.md"],
        "04_Multi_Perspective_Information_Theory": [
            "04.1_Engineering_Communication.md", "04.2_Physics_Information.md", 
            "04.3_Biology_Information.md", "04.4_Algorithm_Complexity.md",
            "04.5_Economics_Information.md", "04.6_Social_Network_Information.md",
            "04.7_Philosophy_Information.md", "04.8_Art_Information.md"
        ],
        "05_Philosophy_of_Science": [
            "05.1_Verification_Falsification.md", "05.2_Underdetermination_Theory.md",
            "05.3_Scientific_Reduction.md", "05.4_Emergence_Theory.md",
            "05.5_Philosophy_Linguistics.md", "05.6_Philosophy_Mathematics.md"
        ],
        "06_Natural_Sciences": [
            "06.1_Physics_Information.md", "06.2_Chemistry_Information.md",
            "06.3_Biology_Information.md"
        ],
        "07_Artificial_Intelligence": ["07.1_AI_Information_Theory.md"],
        "10_Biological_Information_Theory": ["10.1_Genetic_Information.md"]
    }
    
    total = 0
    fixed = 0
    
    for chapter, files in chapters.items():
        print(f"\n📁 {chapter}")
        for filename in files:
            file_path = base_dir / chapter / filename
            if file_path.exists():
                total += 1
                if fix_duplicate_toc(file_path):
                    fixed += 1
            else:
                print(f"⚠️  文件不存在: {filename}")
    
    print(f"\n" + "="*50)
    print(f"✅ 修复完成: {fixed}/{total} 个文件")
    print(f"📊 剩余总进度: {9 + fixed + 1}/36")

if __name__ == "__main__":
    main()

