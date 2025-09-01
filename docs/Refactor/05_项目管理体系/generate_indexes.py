import os
import re
import sys
import argparse
from pathlib import Path
from datetime import datetime

# 约定：
# - 扫描 docs/Refactor 下的所有目录与 Markdown 文件（.md）
# - 生成：
#   1) 00_Master_Index/Auto_Index.md    —— 总目录（按目录层级树 + 每级 README 优先）
#   2) 00_Master_Index/Cross_Reference_Index.md —— 交叉索引（按主题、编号、文件名关键字）
# - 忽略：隐藏目录、node_modules、.git 等常见无关路径
# - 链接：统一使用相对路径（从 00_Master_Index 出发）

ROOT = Path(__file__).resolve().parent
REFACTOR_DIR = ROOT
MASTER_INDEX_DIR = REFACTOR_DIR / "00_Master_Index"
AUTO_INDEX_MD = MASTER_INDEX_DIR / "Auto_Index.md"
CROSS_REF_MD = MASTER_INDEX_DIR / "Cross_Reference_Index.md"

IGNORED_DIR_NAMES = {
    ".git", "node_modules", "__pycache__", ".venv", "venv", ".idea", ".vscode"
}

MD_EXT = {".md", ".MD", ".markdown"}

TITLE_RE = re.compile(r"^\s*#\s+(.+?)\s*$")
HEADING_RE = re.compile(r"^\s{0,3}#{1,6}\s+(.+?)\s*$")

KEYWORDS_MAP = {
    # 主题关键字到分组标题的简单映射，可按需扩展
    "logic": "Logic / 逻辑",
    "类型": "Type Theory / 类型理论",
    "type": "Type Theory / 类型理论",
    "automata": "Automata / 自动机",
    "grammar": "Grammar / 文法",
    "petri": "Petri Nets / Petri网",
    "control": "Control Theory / 控制理论",
    "database": "Database / 数据库",
    "distributed": "Distributed Systems / 分布式系统",
    "network": "Computer Network / 计算机网络",
    "category": "Category Theory / 范畴论",
    "topology": "Topology / 拓扑",
    "algebra": "Algebra / 代数",
    "analysis": "Analysis / 分析"
}


def is_ignored_dir(path: Path) -> bool:
    return path.name in IGNORED_DIR_NAMES or path.name.startswith('.')


def read_first_heading(md_file: Path) -> str | None:
    try:
        with md_file.open('r', encoding='utf-8', errors='ignore') as f:
            for line in f:
                m = HEADING_RE.match(line)
                if m:
                    return m.group(1).strip()
    except Exception:
        return None
    return None


def sort_key_for_paths(p: Path) -> tuple:
    name = p.name
    # 尝试提取前缀编号，例如 02.07_* 或 03_* 或 10_*
    num_parts = re.findall(r"^((?:\d+\.?)+)_?", name)
    if num_parts:
        # 将 02.07 解析为 (2,7)
        parts = tuple(int(x) for x in re.split(r"\.|_", num_parts[0]) if x.isdigit())
    else:
        parts = (9999,)
    return (parts, name.lower())


def build_tree(base_dir: Path) -> dict:
    tree = {
        "path": base_dir,
        "dirs": [],
        "files": []
    }
    for entry in sorted(base_dir.iterdir(), key=sort_key_for_paths):
        if entry.is_dir():
            if is_ignored_dir(entry):
                continue
            if entry.relative_to(REFACTOR_DIR).parts[:1] == ("00_Master_Index",):
                # 跳过自身输出目录
                continue
            tree["dirs"].append(build_tree(entry))
        else:
            if entry.suffix in MD_EXT:
                # 排除输出文件自身
                if entry.name in {AUTO_INDEX_MD.name, CROSS_REF_MD.name}:
                    continue
                tree["files"].append(entry)
    return tree


def relative_link(target: Path) -> str:
    # 相对 00_Master_Index 目录生成链接
    return os.path.relpath(target, start=MASTER_INDEX_DIR).replace('\\', '/')


def render_tree(tree: dict, level: int = 0) -> list[str]:
    lines: list[str] = []
    path: Path = tree["path"]

    # 当前目录标题（非根时打印）
    if level == 0:
        lines.append(f"# Auto Index / 自动生成总目录")
        lines.append("")
        lines.append(f"生成时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        lines.append("")
        lines.append("---")
        lines.append("")
    else:
        rel = relative_link(path)
        title = path.name
        lines.append(f"{'  ' * (level-1)}- **{title}**: [{rel}]({rel})")

    # 优先列出 README.md
    readme = None
    other_files = []
    for f in tree["files"]:
        if f.name.lower() == "readme.md":
            readme = f
        else:
            other_files.append(f)

    if readme is not None:
        title = read_first_heading(readme) or readme.stem
        link = relative_link(readme)
        indent = '  ' * (level)
        lines.append(f"{indent}- [README] {title} → ({link})")

    for f in other_files:
        title = read_first_heading(f) or f.stem
        link = relative_link(f)
        indent = '  ' * (level)
        lines.append(f"{indent}- {title} ({link})")

    for d in tree["dirs"]:
        lines.extend(render_tree(d, level + 1))

    return lines


def collect_cross_refs(base: Path) -> dict[str, list[tuple[str, Path]]]:
    groups: dict[str, list[tuple[str, Path]]] = {}
    for root, dirs, files in os.walk(base):
        # 过滤目录
        dirs[:] = [d for d in sorted(dirs) if not is_ignored_dir(Path(root) / d)]
        # 跳过 00_Master_Index
        if Path(root).resolve() == MASTER_INDEX_DIR.resolve():
            continue
        for fn in sorted(files):
            p = Path(root) / fn
            if p.suffix not in MD_EXT:
                continue
            if p.name in {AUTO_INDEX_MD.name, CROSS_REF_MD.name}:
                continue
            rel = p.relative_to(REFACTOR_DIR)
            # 分配到分组
            key_assigned = False
            lower_name = p.name.lower()
            for kw, group_name in KEYWORDS_MAP.items():
                if kw in lower_name:
                    groups.setdefault(group_name, []).append((lower_name, p))
                    key_assigned = True
            # 按编号前缀额外分组
            m = re.match(r"^(\d+[._]\d+|\d+)_", rel.parts[0]) if rel.parts else None
            if m:
                groups.setdefault(f"Section {m.group(1)}", []).append((lower_name, p))
            if not key_assigned:
                groups.setdefault("Misc / 其他", []).append((lower_name, p))
    # 各组排序
    for k in list(groups.keys()):
        groups[k] = sorted(groups[k], key=lambda x: (x[0], str(x[1]).lower()))
    return groups


def render_cross_refs(groups: dict[str, list[tuple[str, Path]]]) -> list[str]:
    lines: list[str] = []
    lines.append("# Cross Reference Index / 交叉索引")
    lines.append("")
    lines.append(f"生成时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    lines.append("")
    lines.append("> 根据文件名关键词与目录编号自动分组，供导航与检索使用。")
    lines.append("")
    # 固定顺序：先 Section*, 再预设主题组，最后 Misc
    section_keys = sorted([k for k in groups.keys() if k.startswith("Section ")])
    themed_keys = [v for v in KEYWORDS_MAP.values() if v in groups]
    other_keys = sorted([k for k in groups.keys() if k not in set(section_keys) | set(themed_keys) | {"Misc / 其他"}])
    ordered = section_keys + themed_keys + other_keys
    if "Misc / 其他" in groups:
        ordered.append("Misc / 其他")

    for gk in ordered:
        lines.append(f"## {gk}")
        lines.append("")
        for _, p in groups[gk]:
            title = read_first_heading(p) or p.stem
            link = relative_link(p)
            lines.append(f"- {title} ({link})")
        lines.append("")
    return lines


def write_lines(path: Path, lines: list[str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('w', encoding='utf-8', newline='') as f:
        f.write("\n".join(lines).rstrip() + "\n")


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description="Generate auto index and cross reference for docs/Refactor")
    parser.add_argument("--base", default=str(REFACTOR_DIR), help="Base directory (default: docs/Refactor)")
    args = parser.parse_args(argv)

    base_dir = Path(args.base).resolve()
    if not base_dir.exists():
        print(f"Base directory not found: {base_dir}")
        return 1

    # 构建树并渲染总目录
    tree = build_tree(base_dir)
    auto_index_lines = render_tree(tree)
    write_lines(AUTO_INDEX_MD, auto_index_lines)

    # 收集并渲染交叉索引
    groups = collect_cross_refs(base_dir)
    cross_ref_lines = render_cross_refs(groups)
    write_lines(CROSS_REF_MD, cross_ref_lines)

    print(f"Generated: {AUTO_INDEX_MD}")
    print(f"Generated: {CROSS_REF_MD}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
