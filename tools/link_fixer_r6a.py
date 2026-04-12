#!/usr/bin/env python3
"""
R6-A 关键断链修复工具
修复优先级1和优先级2的关键断链
"""

import os
import re
from pathlib import Path
from collections import defaultdict

class LinkFixer:
    def __init__(self, base_path):
        self.base_path = Path(base_path).resolve()
        self.all_files = {}  # normalized_path -> actual_path
        self.fixes = []
        self.stats = defaultdict(int)
        
    def scan_files(self):
        """扫描所有Markdown文件"""
        for f in self.base_path.rglob('*.md'):
            rel_path = f.relative_to(self.base_path)
            normalized = str(rel_path).replace('\\', '/').lower()
            self.all_files[normalized] = str(rel_path).replace('\\', '/')
            # 同时存储不带.md后缀的版本
            if normalized.endswith('.md'):
                self.all_files[normalized[:-3]] = str(rel_path).replace('\\', '/')
                
    def find_file(self, target_path):
        """查找文件是否存在"""
        normalized = target_path.replace('\\', '/').lower()
        # 直接匹配
        if normalized in self.all_files:
            return self.all_files[normalized]
        # 添加.md后缀再匹配
        if not normalized.endswith('.md'):
            normalized_md = normalized + '.md'
            if normalized_md in self.all_files:
                return self.all_files[normalized_md]
        return None
        
    def resolve_link(self, link_url, current_file):
        """解析链接为目标路径"""
        # 处理锚点
        anchor = None
        if '#' in link_url:
            parts = link_url.split('#', 1)
            link_url = parts[0]
            anchor = parts[1]
            
        if not link_url:
            # 纯锚点链接
            return str(current_file).replace('\\', '/'), anchor
            
        # 解析路径
        if link_url.startswith('/'):
            target = self.base_path / link_url[1:]
        else:
            current_dir = (self.base_path / current_file).parent
            target = current_dir / link_url
            
        try:
            rel_path = target.relative_to(self.base_path)
            return str(rel_path).replace('\\', '/'), anchor
        except:
            return None, None
            
    def get_correct_path(self, target_path, anchor=None):
        """尝试找到正确的路径"""
        if target_path is None:
            return None
            
        # 检查文件是否存在
        found = self.find_file(target_path)
        if found:
            if anchor:
                return f"{found}#{anchor}"
            return found
            
        # 尝试常见修复
        # 1. 修复调度系统内部路径
        scheduler_fixes = self._fix_scheduler_paths(target_path)
        for fix in scheduler_fixes:
            found = self.find_file(fix)
            if found:
                if anchor:
                    return f"{found}#{anchor}"
                return found
                
        # 2. 修复FormalRE路径
        formalre_fix = self._fix_formalre_path(target_path)
        if formalre_fix:
            found = self.find_file(formalre_fix)
            if found:
                if anchor:
                    return f"{found}#{anchor}"
                return found
                
        # 3. 修复Matter路径
        matter_fix = self._fix_matter_path(target_path)
        if matter_fix:
            found = self.find_file(matter_fix)
            if found:
                if anchor:
                    return f"{found}#{anchor}"
                return found
                
        return None
        
    def _fix_scheduler_paths(self, target_path):
        """修复调度系统内部路径"""
        fixes = []
        
        # 文件名映射表
        file_mapping = {
            '01.1_调度问题定义.md': '01.1_调度模型抽象.md',
            '01.2_调度算法分析.md': '01.2_调度复杂性.md',
            '01.3_调度等价性.md': '01.3_调度分类学.md',
            '02.1_CPU调度.md': '02.1_CPU调度.md',  # 不变
            '02.2_内存调度.md': '02.2_GPU调度.md',
            '02.3_存储调度.md': '02.3_加速器调度.md',
            '02.4_网络调度.md': '02.4_网络调度.md',  # 可能不存在
            '03.1_进程调度.md': '03.1_进程调度.md',
            '03.2_线程调度.md': '03.2_内存调度.md',
            '03.3_内存管理.md': '03.3_IO调度.md',
            '03.4_设备调度.md': '03.4_设备调度.md',
            '04.1_集群调度.md': '04.1_集群调度.md',
            '04.2_数据流调度.md': '04.2_大数据调度.md',
            '04.3_任务调度.md': '04.3_任务调度.md',
            '04.4_边缘调度.md': '04.4_边缘调度.md',
            '04.3_跨层调度协同.md': '04.3_跨层调度协同.md',
        }
        
        for old, new in file_mapping.items():
            if old in target_path:
                fixes.append(target_path.replace(old, new))
                
        return fixes
        
    def _fix_formalre_path(self, target_path):
        """修复FormalRE路径"""
        # 从调度系统引用FormalRE: ../../FormalRE/...
        if '../../formalre/' in target_path.lower():
            # 实际路径应该是 ../../../FormalRE/
            return target_path.replace('../../FormalRE/', '../../../FormalRE/').replace('../../formalre/', '../../../FormalRE/')
        if '../formalre/' in target_path.lower():
            return target_path.replace('../FormalRE/', '../../FormalRE/').replace('../formalre/', '../../FormalRE/')
        return None
        
    def _fix_matter_path(self, target_path):
        """修复Matter路径"""
        # Matter目录实际存在于 docs/Refactor/Matter/
        # 从调度系统引用: ../../Matter/...
        # 这应该是正确的路径
        if '../../matter/' in target_path.lower():
            corrected = target_path.replace('../../Matter/', '../../Matter/').replace('../../matter/', '../../Matter/')
            return corrected
        return target_path if 'matter' in target_path.lower() else None
        
    def fix_file(self, file_path, dry_run=True):
        """修复单个文件中的断链"""
        try:
            content = file_path.read_text(encoding='utf-8')
            original_content = content
            rel_path = file_path.relative_to(self.base_path)
            rel_path_str = str(rel_path).replace('\\', '/')
            
            changes = []
            
            # 查找所有Markdown链接
            def replace_link(match):
                text, url = match.groups()
                
                # 跳过外部链接
                if url.startswith(('http://', 'https://', 'mailto:', 'tel:')):
                    return match.group(0)
                    
                # 解析链接
                target_path, anchor = self.resolve_link(url, rel_path)
                
                if target_path:
                    # 检查文件是否存在
                    found = self.find_file(target_path)
                    if not found:
                        # 尝试修复
                        corrected = self.get_correct_path(target_path, anchor)
                        if corrected and corrected != url:
                            # 计算相对路径
                            target_abs = self.base_path / corrected.replace('#', '\n').split('\n')[0]
                            if '#' in corrected:
                                corrected_path = corrected.split('#')[0]
                                anchor_part = '#' + corrected.split('#')[1]
                            else:
                                corrected_path = corrected
                                anchor_part = ''
                                
                            current_dir = (self.base_path / rel_path).parent
                            try:
                                new_rel = Path(corrected_path).relative_to(current_dir)
                                new_url = str(new_rel).replace('\\', '/') + anchor_part
                                
                                changes.append({
                                    'old': url,
                                    'new': new_url,
                                    'file': rel_path_str
                                })
                                return f'[{text}]({new_url})'
                            except:
                                pass
                                
                return match.group(0)
                
            # 替换Markdown链接
            new_content = re.sub(r'\[([^\]]+)\]\(([^)]+)\)', replace_link, content)
            
            if changes and not dry_run:
                file_path.write_text(new_content, encoding='utf-8')
                
            return changes
            
        except Exception as e:
            print(f"Error processing {file_path}: {e}")
            return []
            
    def fix_priority1(self, dry_run=True):
        """修复优先级1的断链"""
        scheduler_dirs = [
            self.base_path / "docs/Refactor/06_调度系统",
        ]
        
        all_changes = []
        for dir_path in scheduler_dirs:
            if dir_path.exists():
                for f in dir_path.rglob('*.md'):
                    changes = self.fix_file(f, dry_run)
                    all_changes.extend(changes)
                    
        return all_changes
        
    def generate_report(self, changes):
        """生成修复报告"""
        lines = []
        lines.append("# R6-A 关键断链修复报告")
        lines.append("")
        lines.append(f"修复时间: 2026-04-13")
        lines.append(f"修复数量: {len(changes)}")
        lines.append("")
        
        if changes:
            lines.append("## 修复详情")
            lines.append("")
            
            # 按文件分组
            by_file = defaultdict(list)
            for change in changes:
                by_file[change['file']].append(change)
                
            for file, file_changes in sorted(by_file.items()):
                lines.append(f"### {file}")
                for change in file_changes:
                    lines.append(f"- `{change['old']}` → `{change['new']}`")
                lines.append("")
                
        return '\n'.join(lines)


def main():
    import sys
    base_path = sys.argv[1] if len(sys.argv) > 1 else "."
    dry_run = '--apply' not in sys.argv
    
    fixer = LinkFixer(base_path)
    fixer.scan_files()
    
    print(f"扫描到 {len(fixer.all_files)} 个文件")
    print(f"模式: {'干运行 (预览)' if dry_run else '实际修复'}")
    print("")
    
    # 修复优先级1
    changes = fixer.fix_priority1(dry_run=dry_run)
    
    # 生成报告
    report = fixer.generate_report(changes)
    print(report)
    
    # 保存报告
    report_path = Path(base_path) / ".reports" / "r6a_link_fix_report.md"
    report_path.parent.mkdir(exist_ok=True)
    report_path.write_text(report, encoding='utf-8')
    print(f"\n报告已保存至: {report_path}")
    
    return len(changes)


if __name__ == "__main__":
    exit(main())
