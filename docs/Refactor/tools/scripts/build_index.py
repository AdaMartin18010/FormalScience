#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
索引构建脚本 (build_index.py)

功能说明:
-----------
该脚本用于自动构建文档索引，包括:
- 扫描所有 Markdown 文档
- 提取标题层级结构
- 识别关键词和标签
- 生成文档间的交叉引用
- 创建目录索引和搜索索引

使用方法:
-----------
1. 为当前目录构建索引:
   python build_index.py

2. 为指定目录构建索引:
   python build_index.py -d /path/to/docs

3. 生成 JSON 格式的索引:
   python build_index.py -o index.json -f json

4. 生成交叉引用报告:
   python build_index.py --cross-reference

5. 提取特定深度的标题:
   python build_index.py --max-depth 3

参数说明:
-----------
-d, --directory     指定文档目录（默认: 当前目录）
-o, --output        输出索引文件路径
-f, --format        输出格式: markdown, json, yaml（默认: markdown）
--max-depth         提取标题的最大深度（默认: 6）
--cross-reference   生成交叉引用
--keywords          提取关键词
--min-keyword-len   关键词最小长度（默认: 3）
--exclude           排除特定路径（可多次使用）
-v, --verbose       显示详细输出
-h, --help          显示帮助信息

输出文件:
-----------
- INDEX.md: 目录索引
- keywords.json: 关键词索引
- cross_ref.json: 交叉引用映射

作者: FormalScience 文档工具链
版本: 1.0.0
"""

import argparse
import json
import os
import re
import sys
from collections import defaultdict
from dataclasses import dataclass, field, asdict
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple


@dataclass
class HeadingInfo:
    """标题信息"""
    level: int
    text: str
    anchor: str
    line_number: int


@dataclass
class DocumentInfo:
    """文档信息"""
    path: str
    title: str = ""
    headings: List[HeadingInfo] = field(default_factory=list)
    tags: Set[str] = field(default_factory=set)
    keywords: Dict[str, int] = field(default_factory=dict)
    word_count: int = 0
    modified_time: float = 0.0


@dataclass
class CrossReference:
    """交叉引用"""
    source: str
    target: str
    context: str
    line_number: int
    ref_type: str  # 'link', 'mention'


@dataclass
class IndexReport:
    """索引报告"""
    scan_time: str = ""
    base_directory: str = ""
    total_documents: int = 0
    total_headings: int = 0
    documents: List[DocumentInfo] = field(default_factory=list)
    keywords: Dict[str, List[str]] = field(default_factory=dict)
    cross_references: List[CrossReference] = field(default_factory=list)
    tag_index: Dict[str, List[str]] = field(default_factory=dict)


class IndexBuilder:
    """文档索引构建器"""
    
    # 标题匹配正则
    HEADING_PATTERN = re.compile(r'^(#{1,6})\s+(.+)$', re.MULTILINE)
    
    # 标签匹配 (格式: #tag 或 <!-- tag: xxx -->)
    TAG_PATTERN = re.compile(r'#([\w\u4e00-\u9fff]+)', re.UNICODE)
    META_TAG_PATTERN = re.compile(r'<!--\s*tags?\s*:\s*([^>]+)-->', re.IGNORECASE)
    
    # 代码块匹配 (用于排除代码中的内容)
    CODE_BLOCK_PATTERN = re.compile(r'```[\s\S]*?```|`[^`]+`')
    
    # 链接匹配
    LINK_PATTERN = re.compile(r'\[([^\]]+)\]\(([^)]+)\)')
    
    # 停用词
    STOP_WORDS = {
        'the', 'a', 'an', 'is', 'are', 'was', 'were', 'be', 'been', 'being',
        'have', 'has', 'had', 'do', 'does', 'did', 'will', 'would', 'could',
        'should', 'may', 'might', 'must', 'shall', 'can', 'need', 'dare',
        'ought', 'used', 'to', 'of', 'in', 'for', 'on', 'with', 'at', 'by',
        'from', 'as', 'into', 'through', 'during', 'before', 'after',
        'above', 'below', 'between', 'under', 'again', 'further', 'then',
        'once', 'here', 'there', 'when', 'where', 'why', 'how', 'all',
        'each', 'few', 'more', 'most', 'other', 'some', 'such', 'no', 'nor',
        'not', 'only', 'own', 'same', 'so', 'than', 'too', 'very', 'just',
        'and', 'but', 'if', 'or', 'because', 'until', 'while', 'this',
        'that', 'these', 'those', 'i', 'me', 'my', 'myself', 'we', 'our',
        'you', 'your', 'he', 'him', 'his', 'she', 'her', 'it', 'its',
        'they', 'them', 'their', '的', '了', '在', '是', '我', '有', '和',
        '就', '不', '人', '都', '一', '一个', '上', '也', '很', '到', '说',
        '要', '去', '你', '会', '着', '没有', '看', '好', '自己', '这',
    }
    
    def __init__(self, base_dir: Path, max_depth: int = 6,
                 min_keyword_len: int = 3, exclude_paths: Optional[List[str]] = None):
        """
        初始化索引构建器
        
        Args:
            base_dir: 基础文档目录
            max_depth: 提取标题的最大深度
            min_keyword_len: 关键词最小长度
            exclude_paths: 要排除的路径列表
        """
        self.base_dir = Path(base_dir).resolve()
        self.max_depth = max_depth
        self.min_keyword_len = min_keyword_len
        self.exclude_paths = exclude_paths or []
        self.report = IndexReport()
        self.documents: Dict[str, DocumentInfo] = {}
        self.content_cache: Dict[str, str] = {}
        
    def _should_exclude(self, path: Path) -> bool:
        """检查路径是否应该被排除"""
        path_str = str(path)
        # 排除隐藏目录和文件
        if any(part.startswith('.') for part in path.parts):
            return True
        # 排除特定路径
        for exclude in self.exclude_paths:
            if exclude in path_str:
                return True
        return False
    
    def _get_markdown_files(self) -> List[Path]:
        """获取所有 Markdown 文件"""
        md_files = []
        for ext in ['*.md', '*.markdown', '*.MD']:
            md_files.extend(self.base_dir.rglob(ext))
        return sorted([f for f in md_files if not self._should_exclude(f)])
    
    def _load_file(self, file_path: Path) -> str:
        """加载文件内容（带缓存）"""
        str_path = str(file_path)
        if str_path not in self.content_cache:
            try:
                with open(file_path, 'r', encoding='utf-8') as f:
                    self.content_cache[str_path] = f.read()
            except Exception:
                self.content_cache[str_path] = ""
        return self.content_cache[str_path]
    
    def _generate_anchor(self, heading: str) -> str:
        """生成标题锚点"""
        anchor = heading.lower()
        anchor = re.sub(r'[^\w\s-]', '', anchor)
        anchor = re.sub(r'\s+', '-', anchor)
        return anchor.strip('-')
    
    def _extract_headings(self, content: str) -> List[HeadingInfo]:
        """提取文档标题结构"""
        headings = []
        lines = content.split('\n')
        
        for line_num, line in enumerate(lines, 1):
            match = self.HEADING_PATTERN.match(line)
            if match:
                level = len(match.group(1))
                if level <= self.max_depth:
                    text = match.group(2).strip()
                    anchor = self._generate_anchor(text)
                    headings.append(HeadingInfo(
                        level=level,
                        text=text,
                        anchor=anchor,
                        line_number=line_num
                    ))
        
        return headings
    
    def _extract_tags(self, content: str) -> Set[str]:
        """提取文档标签"""
        tags = set()
        
        # 从元数据中提取标签
        for match in self.META_TAG_PATTERN.finditer(content):
            tag_str = match.group(1)
            tags.update(t.strip() for t in tag_str.split(',') if t.strip())
        
        # 从内容中提取标签
        # 移除代码块
        content_without_code = self.CODE_BLOCK_PATTERN.sub('', content)
        for match in self.TAG_PATTERN.finditer(content_without_code):
            tag = match.group(1)
            if len(tag) >= self.min_keyword_len and tag.lower() not in self.STOP_WORDS:
                tags.add(tag)
        
        return tags
    
    def _extract_keywords(self, content: str) -> Dict[str, int]:
        """提取关键词及其频次"""
        keywords = defaultdict(int)
        
        # 移除代码块
        content_without_code = self.CODE_BLOCK_PATTERN.sub('', content)
        
        # 移除 Markdown 标记
        content_clean = re.sub(r'[#*`_\[\](){}|]', ' ', content_without_code)
        
        # 分词并统计
        words = re.findall(r'\b[\w\u4e00-\u9fff]+\b', content_clean)
        
        for word in words:
            word_lower = word.lower()
            if (len(word) >= self.min_keyword_len and 
                word_lower not in self.STOP_WORDS and
                not word.isdigit()):
                keywords[word] += 1
        
        # 只保留频次最高的前50个关键词
        sorted_keywords = sorted(keywords.items(), key=lambda x: x[1], reverse=True)
        return dict(sorted_keywords[:50])
    
    def _extract_links(self, content: str, source_path: str) -> List[CrossReference]:
        """提取文档中的链接"""
        refs = []
        lines = content.split('\n')
        
        for line_num, line in enumerate(lines, 1):
            for match in self.LINK_PATTERN.finditer(line):
                link_text = match.group(1)
                link_target = match.group(2)
                
                # 只处理内部链接
                if not link_target.startswith(('http://', 'https://', 'mailto:')):
                    refs.append(CrossReference(
                        source=source_path,
                        target=link_target,
                        context=link_text,
                        line_number=line_num,
                        ref_type='link'
                    ))
        
        return refs
    
    def _analyze_document(self, file_path: Path) -> Optional[DocumentInfo]:
        """分析单个文档"""
        content = self._load_file(file_path)
        if not content:
            return None
        
        rel_path = str(file_path.relative_to(self.base_dir))
        
        # 提取标题
        headings = self._extract_headings(content)
        title = headings[0].text if headings else file_path.stem
        
        # 提取标签
        tags = self._extract_tags(content)
        
        # 提取关键词
        keywords = self._extract_keywords(content)
        
        # 计算字数
        word_count = len(content.split())
        
        # 获取修改时间
        modified_time = file_path.stat().st_mtime
        
        return DocumentInfo(
            path=rel_path,
            title=title,
            headings=headings,
            tags=tags,
            keywords=keywords,
            word_count=word_count,
            modified_time=modified_time
        )
    
    def _build_cross_references(self):
        """构建交叉引用"""
        for doc_path, doc_info in self.documents.items():
            content = self._load_file(self.base_dir / doc_path)
            refs = self._extract_links(content, doc_path)
            self.report.cross_references.extend(refs)
    
    def _build_keyword_index(self):
        """构建关键词索引"""
        keyword_docs = defaultdict(list)
        
        for doc_path, doc_info in self.documents.items():
            for keyword in doc_info.keywords.keys():
                keyword_docs[keyword].append(doc_path)
        
        self.report.keywords = dict(keyword_docs)
    
    def _build_tag_index(self):
        """构建标签索引"""
        tag_docs = defaultdict(list)
        
        for doc_path, doc_info in self.documents.items():
            for tag in doc_info.tags:
                tag_docs[tag].append(doc_path)
        
        self.report.tag_index = dict(tag_docs)
    
    def run(self) -> IndexReport:
        """运行索引构建"""
        self.report.scan_time = datetime.now().isoformat()
        self.report.base_directory = str(self.base_dir)
        
        # 获取所有 Markdown 文件
        md_files = self._get_markdown_files()
        
        # 分析每个文档
        for file_path in md_files:
            doc_info = self._analyze_document(file_path)
            if doc_info:
                self.documents[doc_info.path] = doc_info
                self.report.documents.append(doc_info)
                self.report.total_headings += len(doc_info.headings)
        
        self.report.total_documents = len(self.report.documents)
        
        # 构建交叉引用
        self._build_cross_references()
        
        # 构建索引
        self._build_keyword_index()
        self._build_tag_index()
        
        return self.report
    
    def print_summary(self, verbose: bool = False):
        """打印摘要"""
        print("\n" + "=" * 70)
        print("                     索引构建报告")
        print("=" * 70)
        print(f"扫描时间: {self.report.scan_time}")
        print(f"基础目录: {self.report.base_directory}")
        print("-" * 70)
        print(f"文档总数:     {self.report.total_documents}")
        print(f"标题总数:     {self.report.total_headings}")
        print(f"关键词数量:   {len(self.report.keywords)}")
        print(f"标签数量:     {len(self.report.tag_index)}")
        print(f"交叉引用:     {len(self.report.cross_references)}")
        print("=" * 70)
        
        if verbose:
            # 打印文档列表
            print("\n📄 文档列表:")
            for doc in sorted(self.report.documents, key=lambda x: x.path):
                print(f"\n  {doc.path}")
                print(f"    标题: {doc.title}")
                print(f"    字数: {doc.word_count}, 标题数: {len(doc.headings)}")
                if doc.tags:
                    print(f"    标签: {', '.join(sorted(doc.tags))}")
            
            # 打印热门关键词
            if self.report.keywords:
                print("\n🔑 热门关键词 (Top 20):")
                keyword_freq = defaultdict(int)
                for doc in self.report.documents:
                    for kw, freq in doc.keywords.items():
                        keyword_freq[kw] += freq
                
                sorted_kw = sorted(keyword_freq.items(), key=lambda x: x[1], reverse=True)
                for i, (kw, freq) in enumerate(sorted_kw[:20], 1):
                    print(f"  {i:2d}. {kw} ({freq})")
            
            # 打印标签
            if self.report.tag_index:
                print("\n🏷️  标签:")
                for tag, docs in sorted(self.report.tag_index.items()):
                    print(f"  #{tag}: {len(docs)} 个文档")
    
    def save_index(self, output_path: str, format_type: str = 'markdown'):
        """保存索引"""
        output_path = Path(output_path)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        
        if format_type == 'json':
            self._save_json_index(output_path)
        elif format_type == 'yaml':
            self._save_yaml_index(output_path)
        else:
            self._save_markdown_index(output_path)
        
        print(f"\n索引已保存到: {output_path}")
    
    def _save_markdown_index(self, output_path: Path):
        """保存 Markdown 格式索引"""
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write("# 文档索引\n\n")
            f.write(f"**生成时间:** {self.report.scan_time}\n\n")
            f.write(f"**文档总数:** {self.report.total_documents}\n")
            f.write(f"**标题总数:** {self.report.total_headings}\n\n")
            
            f.write("---\n\n")
            f.write("## 目录\n\n")
            
            # 按目录分组
            docs_by_dir = defaultdict(list)
            for doc in self.report.documents:
                dir_path = str(Path(doc.path).parent)
                docs_by_dir[dir_path].append(doc)
            
            for dir_path in sorted(docs_by_dir.keys()):
                f.write(f"### {dir_path or '根目录'}\n\n")
                for doc in sorted(docs_by_dir[dir_path], key=lambda x: x.path):
                    f.write(f"- [{doc.title}]({doc.path})\n")
                    # 添加子标题
                    for heading in doc.headings[:5]:  # 只显示前5个标题
                        indent = "  " * (heading.level - 1)
                        f.write(f"{indent}  - [{heading.text}]({doc.path}#{heading.anchor})\n")
                f.write("\n")
            
            # 标签索引
            if self.report.tag_index:
                f.write("---\n\n")
                f.write("## 标签索引\n\n")
                for tag in sorted(self.report.tag_index.keys()):
                    docs = self.report.tag_index[tag]
                    f.write(f"### #{tag}\n\n")
                    for doc_path in sorted(docs):
                        doc = self.documents.get(doc_path)
                        if doc:
                            f.write(f"- [{doc.title}]({doc_path})\n")
                    f.write("\n")
            
            # 关键词索引
            if self.report.keywords:
                f.write("---\n\n")
                f.write("## 关键词索引\n\n")
                for keyword in sorted(self.report.keywords.keys())[:100]:  # 限制数量
                    docs = self.report.keywords[keyword]
                    f.write(f"**{keyword}**: ")
                    f.write(", ".join(f"[{Path(d).stem}]({d})" for d in docs[:5]))
                    f.write("\n\n")
    
    def _save_json_index(self, output_path: Path):
        """保存 JSON 格式索引"""
        report_dict = {
            'metadata': {
                'scan_time': self.report.scan_time,
                'base_directory': self.report.base_directory,
                'total_documents': self.report.total_documents,
                'total_headings': self.report.total_headings,
            },
            'documents': [
                {
                    'path': doc.path,
                    'title': doc.title,
                    'headings': [
                        {
                            'level': h.level,
                            'text': h.text,
                            'anchor': h.anchor,
                            'line': h.line_number
                        }
                        for h in doc.headings
                    ],
                    'tags': list(doc.tags),
                    'keywords': doc.keywords,
                    'word_count': doc.word_count,
                }
                for doc in self.report.documents
            ],
            'keywords': self.report.keywords,
            'tags': self.report.tag_index,
            'cross_references': [
                {
                    'source': ref.source,
                    'target': ref.target,
                    'context': ref.context,
                    'line': ref.line_number,
                    'type': ref.ref_type
                }
                for ref in self.report.cross_references
            ]
        }
        
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(report_dict, f, ensure_ascii=False, indent=2)
    
    def _save_yaml_index(self, output_path: Path):
        """保存 YAML 格式索引"""
        try:
            import yaml
        except ImportError:
            print("警告: 未安装 PyYAML，将保存为 JSON 格式")
            self._save_json_index(output_path.with_suffix('.json'))
            return
        
        report_dict = {
            'metadata': {
                'scan_time': self.report.scan_time,
                'base_directory': self.report.base_directory,
                'total_documents': self.report.total_documents,
                'total_headings': self.report.total_headings,
            },
            'documents': [
                {
                    'path': doc.path,
                    'title': doc.title,
                    'headings': [
                        {
                            'level': h.level,
                            'text': h.text,
                            'anchor': h.anchor,
                            'line': h.line_number
                        }
                        for h in doc.headings
                    ],
                    'tags': list(doc.tags),
                    'keywords': doc.keywords,
                }
                for doc in self.report.documents
            ]
        }
        
        with open(output_path, 'w', encoding='utf-8') as f:
            yaml.dump(report_dict, f, allow_unicode=True, default_flow_style=False)


def main():
    """主函数"""
    parser = argparse.ArgumentParser(
        description='构建文档索引',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
示例:
  %(prog)s                           # 构建当前目录索引
  %(prog)s -d ./docs                 # 构建指定目录索引
  %(prog)s -o index.md -f markdown   # 生成 Markdown 索引
  %(prog)s -o index.json -f json     # 生成 JSON 索引
  %(prog)s --cross-reference         # 生成交叉引用
        """
    )
    
    parser.add_argument(
        '-d', '--directory',
        default='.',
        help='文档目录（默认: 当前目录）'
    )
    parser.add_argument(
        '-o', '--output',
        help='输出索引文件路径'
    )
    parser.add_argument(
        '-f', '--format',
        choices=['markdown', 'json', 'yaml'],
        default='markdown',
        help='输出格式（默认: markdown）'
    )
    parser.add_argument(
        '--max-depth',
        type=int,
        default=6,
        help='提取标题的最大深度（默认: 6）'
    )
    parser.add_argument(
        '--cross-reference',
        action='store_true',
        help='生成交叉引用'
    )
    parser.add_argument(
        '--min-keyword-len',
        type=int,
        default=3,
        help='关键词最小长度（默认: 3）'
    )
    parser.add_argument(
        '--exclude',
        action='append',
        default=[],
        help='排除特定路径（可多次使用）'
    )
    parser.add_argument(
        '-v', '--verbose',
        action='store_true',
        help='显示详细输出'
    )
    
    args = parser.parse_args()
    
    # 检查目录
    base_dir = Path(args.directory)
    if not base_dir.exists():
        print(f"错误: 目录不存在: {base_dir}", file=sys.stderr)
        sys.exit(1)
    
    if not base_dir.is_dir():
        print(f"错误: 不是目录: {base_dir}", file=sys.stderr)
        sys.exit(1)
    
    # 创建构建器并运行
    builder = IndexBuilder(
        base_dir=base_dir,
        max_depth=args.max_depth,
        min_keyword_len=args.min_keyword_len,
        exclude_paths=args.exclude
    )
    
    print(f"开始构建索引...")
    print(f"目录: {base_dir.resolve()}")
    
    report = builder.run()
    
    # 打印摘要
    builder.print_summary(verbose=args.verbose)
    
    # 保存索引
    if args.output:
        builder.save_index(args.output, args.format)
    else:
        # 默认保存为 INDEX.md
        default_output = base_dir / 'INDEX.md'
        builder.save_index(str(default_output), 'markdown')
    
    sys.exit(0)


if __name__ == '__main__':
    main()
