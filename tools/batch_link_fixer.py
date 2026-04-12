#!/usr/bin/env python3
"""
R6-A 批量断链修复工具
针对优先级1（调度系统）和优先级2的关键断链进行批量修复
"""

import os
import re
from pathlib import Path
from collections import defaultdict

# 文件名映射表 - 将错误链接映射到正确文件
FILE_NAME_MAPPING = {
    # 调度理论基础
    '01.1_调度问题定义.md': '01.1_调度模型抽象.md',
    '01.2_调度算法分析.md': '01.2_调度复杂性.md',
    '01.3_调度等价性.md': '01.3_调度分类学.md',
    
    # 硬件调度  
    '02.2_内存调度.md': '02.2_GPU调度.md',
    '02.3_存储调度.md': '02.3_加速器调度.md',
    
    # OS调度
    '03.2_线程调度.md': '03.2_内存调度.md',
    '03.3_内存管理.md': '03.3_IO调度.md',
    
    # 分布式调度
    '04.2_数据流调度.md': '04.2_大数据调度.md',
}

# 目录结构修正映射
DIR_MAPPING = {
    # FormalRE 路径修正 - 从调度系统看，FormalRE在根目录
    '../../FormalRE/': '../../../FormalRE/',
    '../FormalRE/': '../../FormalRE/',
}


class BatchLinkFixer:
    def __init__(self, base_path):
        self.base_path = Path(base_path).resolve()
        self.all_files = {}  # normalized -> actual
        self.fixes_log = []
        self.stats = {'checked': 0, 'fixed': 0, 'skipped': 0}
        
    def scan_all_files(self):
        """扫描所有文件"""
        print("正在扫描所有Markdown文件...")
        for f in self.base_path.rglob('*.md'):
            rel = str(f.relative_to(self.base_path)).replace('\\', '/')
            normalized = rel.lower()
            self.all_files[normalized] = rel
            # 不带后缀版本
            if normalized.endswith('.md'):
                self.all_files[normalized[:-3]] = rel
        print(f"  找到 {len(self.all_files)//2} 个唯一文件")
        
    def file_exists(self, path):
        """检查文件是否存在"""
        normalized = path.replace('\\', '/').lower()
        if normalized in self.all_files:
            return True
        if not normalized.endswith('.md'):
            if (normalized + '.md') in self.all_files:
                return True
        return False
        
    def get_actual_path(self, path):
        """获取实际路径"""
        normalized = path.replace('\\', '/').lower()
        if normalized in self.all_files:
            return self.all_files[normalized]
        if not normalized.endswith('.md'):
            if (normalized + '.md') in self.all_files:
                return self.all_files[normalized + '.md']
        return None
        
    def fix_link(self, url, current_file):
        """
        修复单个链接
        返回: (fixed_url, was_fixed)
        """
        # 跳过外部链接
        if url.startswith(('http://', 'https://', 'mailto:', 'tel:')):
            return url, False
            
        # 分离锚点
        anchor = ''
        if '#' in url:
            url, anchor = url.split('#', 1)
            anchor = '#' + anchor
            
        if not url:
            return anchor, False
            
        # 解析为绝对路径 (使用resolve()处理..)
        current_dir = (self.base_path / current_file).parent
        if url.startswith('/'):
            target = self.base_path / url[1:]
        else:
            target = (current_dir / url).resolve()
            
        try:
            rel_target = target.relative_to(self.base_path)
            target_str = str(rel_target).replace('\\', '/')
        except:
            return url + anchor, False
            
        # 检查文件是否存在
        if self.file_exists(target_str):
            return url + anchor, False
            
        # 尝试修复
        fixed_url = self._try_fix_url(url, target_str, current_file)
        if fixed_url and fixed_url != url:
            return fixed_url + anchor, True
            
        return url + anchor, False
        
    def _try_fix_url(self, url, target_str, current_file):
        """尝试修复URL"""
        # 1. 尝试文件名映射
        for wrong, correct in FILE_NAME_MAPPING.items():
            if wrong in target_str:
                candidate = target_str.replace(wrong, correct)
                if self.file_exists(candidate):
                    # 计算相对路径
                    return self._make_relative(candidate, current_file)
                    
        # 2. 尝试目录映射 (FormalRE)
        for wrong_dir, correct_dir in DIR_MAPPING.items():
            if wrong_dir in url:
                candidate = url.replace(wrong_dir, correct_dir)
                # 解析并检查
                current_dir = (self.base_path / current_file).parent
                test_target = current_dir / candidate
                try:
                    test_rel = str(test_target.relative_to(self.base_path)).replace('\\', '/')
                    if self.file_exists(test_rel):
                        return candidate
                except:
                    pass
                    
        return None
        
    def _make_relative(self, target_path, current_file):
        """将目标路径转换为相对于当前文件的相对路径"""
        current_dir = (self.base_path / current_file).parent
        target = self.base_path / target_path
        
        try:
            rel = target.relative_to(current_dir)
            return str(rel).replace('\\', '/')
        except:
            return None
            
    def process_file(self, file_path, dry_run=True):
        """处理单个文件"""
        try:
            content = file_path.read_text(encoding='utf-8')
            original = content
            rel_path = str(file_path.relative_to(self.base_path)).replace('\\', '/')
            
            changes = []
            
            # 替换Markdown链接
            def replace_link(match):
                text, url = match.groups()
                fixed, was_fixed = self.fix_link(url, rel_path)
                if was_fixed:
                    changes.append({
                        'old': url,
                        'new': fixed,
                        'text': text[:30]
                    })
                return f'[{text}]({fixed})'
                
            new_content = re.sub(r'\[([^\]]+)\]\(([^)]+)\)', replace_link, content)
            
            # 保存修改
            if changes and not dry_run:
                file_path.write_text(new_content, encoding='utf-8')
                
            return changes
            
        except Exception as e:
            print(f"  错误处理 {file_path}: {e}")
            return []
            
    def fix_priority1_scheduler(self, dry_run=True):
        """修复调度系统（优先级1）"""
        print(f"\n=== 修复优先级1: 调度系统 ===")
        scheduler_dir = self.base_path / "docs/Refactor/06_调度系统"
        
        if not scheduler_dir.exists():
            print("  调度系统目录不存在")
            return []
            
        all_changes = []
        files = list(scheduler_dir.rglob('*.md'))
        print(f"  扫描 {len(files)} 个文件...")
        
        for f in files:
            changes = self.process_file(f, dry_run)
            all_changes.extend([{**c, 'file': str(f.relative_to(self.base_path)).replace('\\', '/')} for c in changes])
            
        print(f"  修复 {len(all_changes)} 个链接")
        return all_changes
        
    def fix_priority2_network(self, dry_run=True):
        """修复网络协议（优先级2）"""
        print(f"\n=== 修复优先级2: 网络协议 ===")
        network_dir = self.base_path / "docs/Refactor/网络协议"
        
        if not network_dir.exists():
            print("  网络协议目录不存在")
            return []
            
        all_changes = []
        files = list(network_dir.rglob('*.md'))
        print(f"  扫描 {len(files)} 个文件...")
        
        for f in files:
            changes = self.process_file(f, dry_run)
            all_changes.extend([{**c, 'file': str(f.relative_to(self.base_path)).replace('\\', '/')} for c in changes])
            
        print(f"  修复 {len(all_changes)} 个链接")
        return all_changes
        
    def generate_report(self, all_changes):
        """生成修复报告"""
        lines = []
        lines.append("# R6-A 关键断链修复报告")
        lines.append("")
        lines.append(f"**修复日期**: 2026-04-13")
        lines.append(f"**修复总数**: {len(all_changes)} 个断链")
        lines.append("")
        
        if not all_changes:
            lines.append("未发现需要修复的断链。")
            return '\n'.join(lines)
            
        # 按文件分组
        by_file = defaultdict(list)
        for change in all_changes:
            by_file[change['file']].append(change)
            
        lines.append("## 修复详情")
        lines.append("")
        
        for file, changes in sorted(by_file.items()):
            lines.append(f"### {file}")
            for c in changes:
                lines.append(f"- `[{c['text']}]` `{c['old']}` → `{c['new']}`")
            lines.append("")
            
        # 统计
        lines.append("## 统计")
        lines.append("")
        lines.append(f"- 涉及文件数: {len(by_file)}")
        lines.append(f"- 修复链接数: {len(all_changes)}")
        lines.append("")
        
        return '\n'.join(lines)


def main():
    import sys
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    flags = [a for a in sys.argv[1:] if a.startswith('--')]
    
    base_path = args[0] if args else "."
    dry_run = '--apply' not in flags
    priority1_only = '--p1' in flags
    
    fixer = BatchLinkFixer(base_path)
    fixer.scan_all_files()
    
    print(f"基础路径: {fixer.base_path}")
    print(f"运行模式: {'干运行 (预览)' if dry_run else '实际修复'}")
    print(f"修复范围: {'仅优先级1' if priority1_only else '优先级1+2'}")
    
    # 修复优先级1
    changes1 = fixer.fix_priority1_scheduler(dry_run)
    
    # 修复优先级2
    changes2 = []
    if not priority1_only:
        changes2 = fixer.fix_priority2_network(dry_run)
        
    all_changes = changes1 + changes2
    
    # 生成报告
    report = fixer.generate_report(all_changes)
    print("\n" + "="*60)
    print(report)
    
    # 保存报告
    report_path = Path(base_path) / ".reports" / "r6a_link_fix_report.md"
    report_path.parent.mkdir(exist_ok=True)
    report_path.write_text(report, encoding='utf-8')
    print(f"\n报告已保存: {report_path}")
    
    if dry_run and all_changes:
        print(f"\n提示: 使用 --apply 参数执行实际修复")
        
    return len(all_changes)


if __name__ == "__main__":
    exit(main())
