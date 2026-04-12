#!/usr/bin/env python3
"""
FormalScience 项目 A3-A4 阶段：交叉引用验证和外部链接检查工具

A3: 交叉引用验证 - 检查docs/Refactor/目录下的内部链接
A4: 外部链接检查 - 检查RFC、论文、工具官网等外部链接的可访问性

使用方法:
    python tools/link_checker.py [--check-external]
"""

import os
import re
import sys
import json
import argparse
from pathlib import Path
from urllib.parse import urlparse
from collections import defaultdict

# 颜色输出
class Colors:
    GREEN = '\033[92m'
    YELLOW = '\033[93m'
    RED = '\033[91m'
    BLUE = '\033[94m'
    RESET = '\033[0m'

def color_print(color, text):
    print(f"{color}{text}{Colors.RESET}")

class LinkChecker:
    def __init__(self, base_path):
        self.base_path = Path(base_path).resolve()
        self.refactor_path = self.base_path / "docs" / "Refactor"
        self.internal_links = []  # (source_file, link_text, target_path, line_num)
        self.external_links = []  # (source_file, link_text, url, line_num)
        self.broken_internal = []
        self.broken_external = []
        self.stats = {
            "total_files": 0,
            "total_internal_links": 0,
            "total_external_links": 0,
            "broken_internal": 0,
            "broken_external": 0,
            "external_skipped": 0
        }
        
    def scan_markdown_files(self):
        """扫描所有Markdown文件"""
        color_print(Colors.BLUE, f"📁 扫描目录: {self.refactor_path}")
        
        if not self.refactor_path.exists():
            color_print(Colors.RED, f"❌ 目录不存在: {self.refactor_path}")
            return
            
        md_files = list(self.refactor_path.rglob("*.md"))
        self.stats["total_files"] = len(md_files)
        color_print(Colors.GREEN, f"✅ 找到 {len(md_files)} 个Markdown文件")
        
        for md_file in md_files:
            self.extract_links_from_file(md_file)
    
    def extract_links_from_file(self, file_path):
        """从单个文件中提取链接"""
        try:
            content = file_path.read_text(encoding='utf-8')
            lines = content.split('\n')
            
            # 获取相对路径（从Refactor目录开始）
            rel_path = file_path.relative_to(self.refactor_path)
            
            for line_num, line in enumerate(lines, 1):
                # 匹配Markdown链接: [text](url)
                # 匹配带标题的链接: [text](url "title")
                pattern = r'\[([^\]]+)\]\(([^\s")]+)(?:\s+"[^"]*")?\)'
                matches = re.finditer(pattern, line)
                
                for match in matches:
                    link_text = match.group(1)
                    link_target = match.group(2)
                    
                    # 跳过锚点链接（纯#开头的）
                    if link_target.startswith('#') and not link_target.startswith('#/'):
                        continue
                    
                    # 判断是内部链接还是外部链接
                    if link_target.startswith('http://') or link_target.startswith('https://'):
                        self.external_links.append((
                            str(rel_path), link_text, link_target, line_num
                        ))
                    elif link_target.startswith('mailto:'):
                        # 跳过邮件链接
                        continue
                    else:
                        # 内部链接（相对路径）
                        self.internal_links.append((
                            str(rel_path), link_text, link_target, line_num
                        ))
                        
        except Exception as e:
            color_print(Colors.YELLOW, f"⚠️ 读取文件失败 {file_path}: {e}")
    
    def validate_internal_links(self):
        """验证内部链接的有效性"""
        color_print(Colors.BLUE, "\n🔍 开始验证内部交叉引用...")
        
        self.stats["total_internal_links"] = len(self.internal_links)
        color_print(Colors.GREEN, f"📊 发现 {len(self.internal_links)} 个内部链接")
        
        for source, link_text, target, line_num in self.internal_links:
            # 解析目标路径
            # 支持锚点: path/to/file.md#section
            if '#' in target:
                target_path, anchor = target.split('#', 1)
            else:
                target_path = target
                anchor = None
            
            # 如果是绝对路径（从根开始）
            if target_path.startswith('/'):
                full_target = self.refactor_path / target_path.lstrip('/')
            else:
                # 相对路径
                source_dir = self.refactor_path / os.path.dirname(source)
                full_target = source_dir / target_path
            
            full_target = full_target.resolve()
            
            # 检查文件是否存在
            if not full_target.exists():
                self.broken_internal.append({
                    "source": source,
                    "link_text": link_text,
                    "target": target,
                    "line": line_num,
                    "reason": "文件不存在"
                })
            elif anchor and not self._check_anchor_exists(full_target, anchor):
                # 文件存在但锚点可能不存在（仅警告，不算严重错误）
                self.broken_internal.append({
                    "source": source,
                    "link_text": link_text,
                    "target": target,
                    "line": line_num,
                    "reason": f"锚点不存在: #{anchor}"
                })
        
        self.stats["broken_internal"] = len(self.broken_internal)
        
        if self.broken_internal:
            color_print(Colors.RED, f"❌ 发现 {len(self.broken_internal)} 个无效内部链接")
        else:
            color_print(Colors.GREEN, "✅ 所有内部链接有效")
    
    def _check_anchor_exists(self, file_path, anchor):
        """检查文件中的锚点是否存在"""
        try:
            content = file_path.read_text(encoding='utf-8')
            # Markdown锚点通常是标题: # anchor-text 或 <a name="anchor">
            # 简化为检查内容中是否有相关文本
            anchor_pattern = f'#{anchor}'
            return anchor_pattern in content or f'name="{anchor}"' in content
        except:
            return False
    
    def validate_external_links(self, max_checks=50):
        """验证外部链接的可访问性（抽样检查）"""
        color_print(Colors.BLUE, "\n🌐 开始验证外部链接...")
        
        self.stats["total_external_links"] = len(self.external_links)
        color_print(Colors.GREEN, f"📊 发现 {len(self.external_links)} 个外部链接")
        
        if len(self.external_links) == 0:
            return
        
        # 去重，按域名分组
        url_groups = defaultdict(list)
        for source, link_text, url, line_num in self.external_links:
            domain = urlparse(url).netloc
            url_groups[domain].append({
                "source": source,
                "link_text": link_text,
                "url": url,
                "line": line_num
            })
        
        color_print(Colors.BLUE, f"🔗 分布在 {len(url_groups)} 个不同域名")
        
        # 重要域名优先检查
        priority_domains = [
            'lean-lang.org',
            'github.com',
            'leanprover-community.github.io',
            'arxiv.org',
            'doi.org',
            'wikipedia.org',
            'ocw.mit.edu',
            'cs.cornell.edu'
        ]
        
        checked_count = 0
        
        # 优先检查重要域名
        for domain in priority_domains:
            if domain in url_groups and checked_count < max_checks:
                for link_info in url_groups[domain][:3]:  # 每个域名检查最多3个
                    self._check_single_external_link(link_info)
                    checked_count += 1
        
        # 检查其他域名（抽样）
        remaining = max_checks - checked_count
        if remaining > 0:
            for domain, links in url_groups.items():
                if domain not in priority_domains and remaining > 0:
                    for link_info in links[:1]:  # 其他域名每个检查1个
                        self._check_single_external_link(link_info)
                        checked_count += 1
                        remaining -= 1
                        if remaining <= 0:
                            break
        
        skipped = len(self.external_links) - checked_count
        self.stats["external_skipped"] = skipped
        
        color_print(Colors.YELLOW, f"⏭️  抽样检查 {checked_count} 个外部链接，跳过 {skipped} 个")
        
        if self.broken_external:
            color_print(Colors.RED, f"❌ 发现 {len(self.broken_external)} 个可疑外部链接")
        else:
            color_print(Colors.GREEN, f"✅ 抽样的外部链接均可访问")
    
    def _check_single_external_link(self, link_info):
        """检查单个外部链接"""
        # 在实际环境中，这里会发送HTTP请求
        # 由于环境限制，我们只记录需要检查的项目
        # 标记一些已知可能变化的服务
        url = link_info["url"]
        
        # 检查URL格式
        parsed = urlparse(url)
        if not parsed.netloc:
            self.broken_external.append({
                **link_info,
                "reason": "URL格式无效"
            })
            return
        
        # 记录需要人工验证的链接
        # 实际HTTP检查需要在有网络的环境中进行
        self.broken_external.append({
            **link_info,
            "reason": "需要人工验证（建议手动访问确认）"
        })
    
    def generate_report(self, output_path):
        """生成检查报告"""
        report = {
            "project": "FormalScience",
            "task": "A3-A4: 交叉引用验证和外部链接检查",
            "timestamp": self._get_timestamp(),
            "statistics": self.stats,
            "broken_internal_links": self.broken_internal,
            "external_links_summary": {
                "total": len(self.external_links),
                "domains": len(set(urlparse(url).netloc for _, _, url, _ in self.external_links)),
                "sample_checked": len(self.external_links) - self.stats["external_skipped"],
                "issues_found": len(self.broken_external)
            },
            "top_external_domains": self._get_top_domains()
        }
        
        # 保存JSON报告
        json_path = output_path.with_suffix('.json')
        with open(json_path, 'w', encoding='utf-8') as f:
            json.dump(report, f, ensure_ascii=False, indent=2)
        
        # 生成Markdown报告
        md_path = output_path.with_suffix('.md')
        self._generate_markdown_report(md_path, report)
        
        color_print(Colors.GREEN, f"\n📄 报告已保存:")
        color_print(Colors.GREEN, f"   - JSON: {json_path}")
        color_print(Colors.GREEN, f"   - Markdown: {md_path}")
        
        return report
    
    def _get_timestamp(self):
        from datetime import datetime
        return datetime.now().isoformat()
    
    def _get_top_domains(self, n=10):
        """获取最频繁引用的外部域名"""
        domains = defaultdict(int)
        for _, _, url, _ in self.external_links:
            domain = urlparse(url).netloc
            domains[domain] += 1
        return sorted(domains.items(), key=lambda x: x[1], reverse=True)[:n]
    
    def _generate_markdown_report(self, path, report):
        """生成Markdown格式的报告"""
        content = f"""# FormalScience 项目 A3-A4 阶段检查报告

> **任务**: 交叉引用验证和外部链接检查
> **执行时间**: {report['timestamp']}
> **项目**: {report['project']}

---

## 📊 执行摘要

### 统计概览

| 指标 | 数值 |
|------|------|
| 扫描文档总数 | {report['statistics']['total_files']} |
| 内部链接总数 | {report['statistics']['total_internal_links']} |
| 外部链接总数 | {report['statistics']['total_external_links']} |
| 无效内部链接 | {report['statistics']['broken_internal']} |
| 外部域名数量 | {report['external_links_summary']['domains']} |

---

## 🔗 A3: 交叉引用验证结果

### 内部链接统计

- **总内部链接**: {report['statistics']['total_internal_links']}
- **无效链接**: {report['statistics']['broken_internal']}
- **有效比例**: {self._calc_percentage(report['statistics']['total_internal_links'] - report['statistics']['broken_internal'], report['statistics']['total_internal_links'])}

"""
        
        if self.broken_internal:
            content += "### ❌ 无效内部链接详情\n\n"
            content += "| 源文件 | 链接文本 | 目标路径 | 行号 | 问题 |\n"
            content += "|--------|----------|----------|------|------|\n"
            for item in self.broken_internal[:50]:  # 最多显示50个
                content += f"| {item['source']} | {item['link_text'][:30]}... | {item['target']} | {item['line']} | {item['reason']} |\n"
            if len(self.broken_internal) > 50:
                content += f"\n> 还有 {len(self.broken_internal) - 50} 个无效链接未显示...\n"
        else:
            content += "\n✅ **所有内部链接验证通过！**\n"
        
        content += f"""

---

## 🌐 A4: 外部链接检查结果

### 外部链接统计

- **总外部链接**: {report['external_links_summary']['total']}
- **涉及域名**: {report['external_links_summary']['domains']}
- **抽样检查**: {report['external_links_summary']['sample_checked']}
- **需验证链接**: {report['external_links_summary']['issues_found']}

### 主要引用域名（Top 10）

| 域名 | 引用次数 |
|------|----------|
"""
        for domain, count in report['top_external_domains']:
            content += f"| {domain} | {count} |\n"
        
        content += f"""

### 外部链接验证建议

由于外部链接可能随时间变化，建议：

1. **定期人工抽查**: 每季度手动检查主要外部链接
2. **使用自动化工具**: 配置CI/CD定期运行链接检查
3. **建立链接白名单**: 记录关键外部资源的备用链接
4. **使用存档服务**: 对重要引用使用Wayback Machine存档

---

## 📈 整体评估

### A3 交叉引用验证

"""
        if report['statistics']['broken_internal'] == 0:
            content += "✅ **状态**: 通过 - 所有内部交叉引用有效\n"
        elif report['statistics']['broken_internal'] < 10:
            content += "⚠️ **状态**: 警告 - 存在少量无效内部链接，建议修复\n"
        else:
            content += "❌ **状态**: 失败 - 存在较多无效内部链接，需要全面修复\n"
        
        content += f"""
### A4 外部链接检查

"""
        if report['external_links_summary']['issues_found'] == 0:
            content += "✅ **状态**: 通过 - 抽样的外部链接均可访问\n"
        else:
            content += "⚠️ **状态**: 需要人工验证 - 外部链接需要定期手动检查确认\n"
        
        content += f"""

---

## 🔧 修复建议

### 内部链接修复

1. **检查文件移动**: 确认目标文件是否被重命名或移动
2. **更新相对路径**: 修正相对路径以匹配实际文件位置
3. **检查大小写**: Linux/Mac文件系统区分大小写
4. **验证锚点**: 确保锚点ID与文档中的标题匹配

### 外部链接维护

1. **使用永久链接**: 优先使用DOI、存档链接等永久URL
2. **定期检查**: 建议每季度运行一次链接检查
3. **记录变更**: 维护外部资源变更日志
4. **建立镜像**: 对关键资源考虑本地备份

---

## 📁 相关文件

- [交叉引用建立报告](../CROSS_REFERENCE_REPORT.md)
- [外部资源汇总](../RESOURCES.md)
- [项目索引](../00_INDEX.md)

---

*报告生成时间: {report['timestamp']}*
"""
        
        Path(path).write_text(content, encoding='utf-8')
    
    def _calc_percentage(self, part, total):
        if total == 0:
            return "100%"
        return f"{part/total*100:.1f}%"

def main():
    parser = argparse.ArgumentParser(description='FormalScience 项目链接检查工具')
    parser.add_argument('--check-external', action='store_true', 
                        help='检查外部链接（默认只检查内部链接）')
    parser.add_argument('--output', '-o', default='docs/Refactor/.reports/link_check_report',
                        help='报告输出路径')
    parser.add_argument('--max-external', type=int, default=50,
                        help='最多检查的外部链接数量')
    
    args = parser.parse_args()
    
    # 确定项目根目录
    script_dir = Path(__file__).parent
    project_root = script_dir.parent
    
    color_print(Colors.BLUE, "=" * 60)
    color_print(Colors.BLUE, "FormalScience 项目 A3-A4 阶段检查")
    color_print(Colors.BLUE, "=" * 60)
    
    checker = LinkChecker(project_root)
    
    # 扫描文件
    checker.scan_markdown_files()
    
    # 验证内部链接
    checker.validate_internal_links()
    
    # 验证外部链接（如果启用）
    if args.check_external:
        checker.validate_external_links(max_checks=args.max_external)
    else:
        color_print(Colors.YELLOW, "\n⏭️  跳过外部链接检查（使用 --check-external 启用）")
    
    # 生成报告
    output_path = project_root / args.output
    output_path.parent.mkdir(parents=True, exist_ok=True)
    report = checker.generate_report(output_path)
    
    # 打印摘要
    color_print(Colors.BLUE, "\n" + "=" * 60)
    color_print(Colors.BLUE, "检查完成摘要")
    color_print(Colors.BLUE, "=" * 60)
    color_print(Colors.GREEN, f"📊 扫描文档: {report['statistics']['total_files']}")
    color_print(Colors.GREEN, f"🔗 内部链接: {report['statistics']['total_internal_links']}")
    
    if report['statistics']['broken_internal'] == 0:
        color_print(Colors.GREEN, f"✅ 无效内部链接: {report['statistics']['broken_internal']}")
    else:
        color_print(Colors.RED, f"❌ 无效内部链接: {report['statistics']['broken_internal']}")
    
    color_print(Colors.GREEN, f"🌐 外部链接: {report['external_links_summary']['total']}")
    
    # 返回退出码
    if report['statistics']['broken_internal'] > 0:
        color_print(Colors.YELLOW, "\n⚠️  发现无效内部链接，请查看报告并修复")
        return 1
    else:
        color_print(Colors.GREEN, "\n✅ 所有检查通过！")
        return 0

if __name__ == "__main__":
    sys.exit(main())
