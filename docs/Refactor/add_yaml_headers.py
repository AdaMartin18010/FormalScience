#!/usr/bin/env python3
"""
为FormalScience项目的docs/Refactor/文档添加YAML元数据头
"""

import os
import re
from pathlib import Path
from datetime import datetime

# 基础目录
BASE_DIR = Path("e:/_src/FormalScience/docs/Refactor")

# 要处理的章节
CHAPTERS = [
    "01_数学基础",
    "02_形式语言", 
    "03_编程范式",
    "04_软件工程",
    "05_形式化理论",
    "06_调度系统",
    "07_交叉视角",
    "08_附录",
    "09_统计学",
    "10_信息论",
    "11_系统科学",
    "12_决策与博弈论",
    "13_认知科学形式模型",
    "14_形式语言学",
    "15_社会科学形式化",
]

# 排除的文件模式
EXCLUDE_PATTERNS = [
    "_index.md",
    "README.md",
    "00_*.md",  # 索引文件
    "*.py",
    "*.json",
    "*.csv",
]

# 难度映射
def infer_difficulty(filepath: Path, content: str) -> str:
    """根据文件路径和内容推断难度"""
    path_str = str(filepath).lower()
    
    # 从路径判断
    if any(x in path_str for x in ["基础", "basic", "入门"]):
        return "初级"
    if any(x in path_str for x in ["进阶", "advanced", "深入"]):
        return "高级"
    
    # 从内容判断
    if "难度级别: 初级" in content or "🎯 **难度级别**: 初级" in content:
        return "初级"
    if "难度级别: 中级" in content or "🎯 **难度级别**: 中级" in content:
        return "中级"
    if "难度级别: 高级" in content or "🎯 **难度级别**: 高级" in content:
        return "高级"
    
    # 默认中级
    return "中级"

def extract_title(content: str) -> str:
    """从内容中提取标题"""
    lines = content.strip().split('\n')
    for line in lines:
        # 匹配一级标题
        match = re.match(r'^#\s+(.+?)$', line.strip())
        if match:
            title = match.group(1).strip()
            # 移除可能的英文后缀
            title = re.sub(r'\s*-\s*[A-Za-z\s]+$', '', title)
            return title
    return "未命名文档"

def extract_tags(content: str, category: str, subcategory: str) -> list:
    """从内容提取标签"""
    tags = []
    
    # 从关键词提取
    keyword_match = re.search(r'\*\*关键词\*\*[:：]\s*(.+?)(?:\n|$)', content)
    if keyword_match:
        keywords = keyword_match.group(1)
        # 分割关键词
        tags = [k.strip() for k in re.split(r'[,，、]\s*', keywords) if k.strip()]
    
    # 添加分类标签
    tags.append(category)
    tags.append(subcategory)
    
    # 去重并限制数量
    unique_tags = list(dict.fromkeys(tags))[:6]
    return unique_tags

def extract_related(content: str) -> list:
    """从内容提取相关文档链接"""
    related = []
    
    # 匹配相关文档、延伸阅读等部分的链接
    patterns = [
        r'- \[([^\]]+)\]\([^)]+\)',  # Markdown链接
        r'\[([^\]]+)\]\([^)]+\)',   # 内联链接
    ]
    
    for pattern in patterns:
        matches = re.findall(pattern, content)
        related.extend(matches[:5])  # 最多5个
    
    return related[:5]

def has_yaml_header(content: str) -> bool:
    """检查是否已有YAML头"""
    lines = content.strip().split('\n')
    if len(lines) >= 3 and lines[0].strip() == '---':
        # 检查是否是真正的YAML头（第二个---在合理位置）
        for i, line in enumerate(lines[1:20], 1):
            if line.strip() == '---':
                # 检查中间是否包含YAML键值对
                yaml_section = '\n'.join(lines[1:i])
                if ':' in yaml_section:
                    return True
    return False

def determine_category_and_subcategory(filepath: Path) -> tuple:
    """根据文件路径确定类别和子类别"""
    parts = filepath.parts
    category = "其他"
    subcategory = "一般"
    
    # 查找章节目录
    for i, part in enumerate(parts):
        if part.startswith(tuple(CHAPTERS)):
            category = part.split('_', 1)[1] if '_' in part else part
            # 子类别
            if i + 1 < len(parts):
                sub = parts[i + 1]
                if '_' in sub:
                    subcategory = sub.split('_', 1)[1]
            break
    
    return category, subcategory

def generate_yaml_header(filepath: Path, content: str) -> str:
    """生成YAML元数据头"""
    title = extract_title(content)
    category, subcategory = determine_category_and_subcategory(filepath)
    difficulty = infer_difficulty(filepath, content)
    tags = extract_tags(content, category, subcategory)
    related = extract_related(content)
    
    # 检测是否包含数学公式
    has_math = '$' in content or '$$' in content or '\\(' in content
    
    # 检测是否包含代码
    has_code = '```' in content
    
    # 构建YAML头
    yaml_lines = [
        "---",
        f'title: "{title}"',
        f'category: "{category}"',
        f'subcategory: "{subcategory}"',
        f'order: {extract_order(filepath)}',
        f'difficulty: "{difficulty}"',
        'status: "已完成"',
        f'tags: {str(tags).replace(chr(39), chr(34))}',
    ]
    
    if related:
        yaml_lines.append(f'related: {str(related).replace(chr(39), chr(34))}')
    
    yaml_lines.extend([
        f'math: {str(has_math).lower()}',
        f'code: {str(has_code).lower()}',
        f'last_updated: "{datetime.now().strftime("%Y-%m-%d")}"',
        "---",
    ])
    
    return '\n'.join(yaml_lines)

def extract_order(filepath: Path) -> int:
    """从文件名提取顺序号"""
    filename = filepath.name
    match = re.match(r'^(\d+)\.', filename)
    if match:
        return int(match.group(1))
    return 1

def should_process_file(filepath: Path) -> bool:
    """判断是否应该处理该文件"""
    # 检查是否在处理的章节中
    in_target_chapter = any(ch in str(filepath) for ch in CHAPTERS)
    if not in_target_chapter:
        return False
    
    # 排除特定文件
    for pattern in EXCLUDE_PATTERNS:
        if filepath.match(pattern):
            return False
    
    # 只处理.md文件
    if not filepath.suffix == '.md':
        return False
    
    return True

def process_file(filepath: Path) -> bool:
    """处理单个文件，添加YAML头"""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # 检查是否已有YAML头
        if has_yaml_header(content):
            print(f"  跳过 (已有YAML头): {filepath}")
            return False
        
        # 生成YAML头
        yaml_header = generate_yaml_header(filepath, content)
        
        # 组合新内容
        new_content = yaml_header + '\n\n' + content
        
        # 写入文件
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(new_content)
        
        print(f"  ✓ 已添加YAML头: {filepath}")
        return True
        
    except Exception as e:
        print(f"  ✗ 错误处理 {filepath}: {e}")
        return False

def main():
    """主函数"""
    print("=" * 60)
    print("FormalScience YAML元数据头添加工具")
    print("=" * 60)
    print()
    
    processed_count = 0
    skipped_count = 0
    error_count = 0
    processed_files = []
    
    # 遍历所有章节
    for chapter in CHAPTERS:
        chapter_dir = BASE_DIR / chapter
        if not chapter_dir.exists():
            print(f"目录不存在: {chapter_dir}")
            continue
        
        print(f"\n处理章节: {chapter}")
        print("-" * 40)
        
        # 遍历目录下的所有.md文件
        for md_file in chapter_dir.rglob("*.md"):
            if should_process_file(md_file):
                if process_file(md_file):
                    processed_count += 1
                    processed_files.append(str(md_file.relative_to(BASE_DIR)))
                else:
                    skipped_count += 1
    
    # 生成报告
    print("\n" + "=" * 60)
    print("处理报告")
    print("=" * 60)
    print(f"成功添加: {processed_count} 个文档")
    print(f"跳过: {skipped_count} 个文档")
    print(f"错误: {error_count} 个文档")
    
    if processed_files:
        print("\n已处理的文件列表:")
        for f in processed_files:
            print(f"  - {f}")
    
    # 保存报告
    report_path = BASE_DIR / ".reports" / "yaml_header_addition_report.md"
    report_path.parent.mkdir(exist_ok=True)
    
    with open(report_path, 'w', encoding='utf-8') as f:
        f.write("# YAML元数据头添加报告\n\n")
        f.write(f"生成时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n\n")
        f.write("## 统计\n\n")
        f.write(f"- 成功添加: {processed_count} 个文档\n")
        f.write(f"- 跳过: {skipped_count} 个文档\n")
        f.write(f"- 错误: {error_count} 个文档\n\n")
        f.write("## 处理的文件列表\n\n")
        for file in processed_files:
            f.write(f"- `{file}`\n")
    
    print(f"\n报告已保存至: {report_path}")

if __name__ == "__main__":
    main()
