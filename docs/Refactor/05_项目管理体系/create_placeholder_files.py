#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
批量创建占位 Markdown 文件，确保 README 中的本地链接有效
"""

import os
import pathlib
from datetime import datetime

def create_placeholder_file(file_path: pathlib.Path, title: str):
    """创建占位文件"""
    content = f"""# {title}

本文档为占位草稿，用于支撑目录 README 的本地链接有效性。

## 提纲

- 基础概念与定义
- 理论框架与证明
- 实现方法与示例
- 应用场景与扩展

---
最后更新: {datetime.now().strftime('%Y-%m-%d')}（占位草稿）
"""
    file_path.parent.mkdir(parents=True, exist_ok=True)
    file_path.write_text(content, encoding='utf-8')

def main():
    root = pathlib.Path(__file__).parent / "03_Formal_Language_Theory" / "03.2_Formal_Grammars"
    
    # 定义需要创建的文件
    files_to_create = {
        '03.2.1_Regular_Grammar_Resources': [
            '01_文法基本概念.md',
            '正则文法基础.md',
            '正则表达式理论.md',
            '正则文法实现.md',
            '正则文法与DFA转换.md',
            '正则文法练习题.md',
            '词法分析器设计.md',
        ],
        '03.2.2_Context_Free_Grammar_Resources': [
            '上下文无关文法基础.md',
            'CFG的形式化定义.md',
            'Chomsky范式.md',
            'Greibach范式.md',
            '递归下降解析器.md',
            'CYK算法.md',
            'Earley算法.md',
            '上下文无关文法练习题.md',
            '语法分析器设计.md',
            '程序设计语言语法.md',
        ],
        '03.2.3_Context_Sensitive_Grammar_Resources': [
            '上下文相关文法基础.md',
            'CSG的形式化定义.md',
            'Kuroda范式.md',
            'CSG解析算法.md',
            'CSG与LBA转换.md',
            '上下文相关文法练习题.md',
            '自然语言语法建模.md',
            '空间复杂性分析.md',
        ],
    }
    
    created_count = 0
    for directory, files in files_to_create.items():
        dir_path = root / directory
        print(f"处理目录: {directory}")
        
        for filename in files:
            file_path = dir_path / filename
            if not file_path.exists():
                title = filename.replace('.md', '')
                create_placeholder_file(file_path, title)
                print(f"  创建: {filename}")
                created_count += 1
            else:
                print(f"  已存在: {filename}")
    
    print(f"\n总计创建了 {created_count} 个占位文件")

if __name__ == "__main__":
    main()
