#!/usr/bin/env python3
"""
FormalScience Quality Gate

Runs on every commit to enforce content standards.
Checks:
  1. Empty/shell document detection
  2. Placeholder detection
  3. Broken link detection (docs/Refactor only)
  4. Lean `sorry` counter
  5. Duplicate directory name detection

Exits with code 0 (PASS) or 1 (FAIL).
"""

from __future__ import annotations

import argparse
import re
import sys
from collections import defaultdict
from pathlib import Path

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

PROJECT_ROOT = Path(__file__).resolve().parent.parent

PLACEHOLDER_PATTERN = re.compile(
    r"待完善|占位(?!符)|placeholder|TODO: 内容待补充",
    re.IGNORECASE,
)

BYPASS_EMPTY_NAMES = {"README.md", "_index.md", "00_目录与导航.md"}

LINK_RE = re.compile(r"\[([^\]]+)\]\(([^)]+)\)")

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def is_header_or_toc_or_empty(line: str) -> bool:
    """Return True if the line is a header, TOC marker, or visually empty."""
    stripped = line.strip()
    if not stripped:
        return True
    if stripped.startswith("#"):
        return True
    if stripped.startswith("-") and "toc" in stripped.lower():
        return True
    if stripped.lower() in {"<!-- toc -->", "<!-- /toc -->"}:
        return True
    return False


def gather_md_files(root: Path) -> list[Path]:
    """Return all *.md files under *root* (recursively)."""
    if not root.exists():
        return []
    return sorted(root.rglob("*.md"))


def dir_has_other_files(directory: Path, excluded_names: set[str]) -> bool:
    """Return True if *directory* contains at least one file not in *excluded_names*."""
    if not directory.is_dir():
        return False
    for child in directory.iterdir():
        if child.is_file() and child.name not in excluded_names:
            return True
    return False


# ---------------------------------------------------------------------------
# Check 1: Empty/Shell Document Detection
# ---------------------------------------------------------------------------


def check_empty_documents(
    dirs: list[Path],
    line_threshold: int = 30,
    substantive_threshold: int = 5,
) -> list[Path]:
    flagged: list[Path] = []
    for d in dirs:
        for fp in gather_md_files(d):
            rel = fp.relative_to(PROJECT_ROOT)
            # Bypass specific index/navigation files if the directory has other content
            if fp.name in BYPASS_EMPTY_NAMES:
                if dir_has_other_files(fp.parent, BYPASS_EMPTY_NAMES):
                    continue

            try:
                lines = fp.read_text(encoding="utf-8").splitlines()
            except Exception:
                continue

            if len(lines) >= line_threshold:
                continue

            substantive = sum(
                1 for line in lines if not is_header_or_toc_or_empty(line)
            )
            if substantive < substantive_threshold:
                flagged.append(rel)

    return flagged


# ---------------------------------------------------------------------------
# Check 2: Placeholder Detection
# ---------------------------------------------------------------------------


def check_placeholders(dirs: list[Path]) -> list[tuple[Path, list[str]]]:
    flagged: list[tuple[Path, list[str]]] = []

    for d in dirs:
        for fp in gather_md_files(d):
            try:
                content = fp.read_text(encoding="utf-8")
            except Exception:
                continue
            matches = PLACEHOLDER_PATTERN.findall(content)
            if matches:
                flagged.append((fp.relative_to(PROJECT_ROOT), matches))

    return flagged


# ---------------------------------------------------------------------------
# Check 3: Broken Link Detection (docs/Refactor only)
# ---------------------------------------------------------------------------


def _normalize_path(part: str) -> str:
    return part.replace("\\", "/")


def check_broken_links(base_dir: Path) -> dict[Path, list[str]]:
    """Check internal relative markdown links inside *base_dir*."""
    broken: dict[Path, list[str]] = defaultdict(list)

    # Build an index of all files (case-insensitive, with and without .md)
    file_index: set[str] = set()
    for fp in base_dir.rglob("*"):
        if fp.is_file():
            rel = _normalize_path(str(fp.relative_to(base_dir)))
            file_index.add(rel.lower())
            if rel.lower().endswith(".md"):
                file_index.add(rel.lower()[:-3])

    md_files = gather_md_files(base_dir)

    for fp in md_files:
        rel_fp = _normalize_path(str(fp.relative_to(base_dir)))
        try:
            content = fp.read_text(encoding="utf-8")
        except Exception:
            continue

        for match in LINK_RE.finditer(content):
            url = match.group(2).strip()

            # Skip external links and anchors-only
            if not url or url.startswith(("http://", "https://", "mailto:", "tel:")):
                continue

            # Skip URLs that look like math/LaTeX (contain backslashes, brackets, etc.)
            if any(ch in url for ch in {"\\", "[", "]", "{", "}", "$", "^"}):
                continue

            # Skip URLs that contain spaces but no path separator (likely notation, not paths)
            if " " in url and "/" not in url:
                continue

            # Strip anchor
            raw_url = url.split("#", 1)[0]
            if not raw_url:
                continue

            # Resolve relative to current file
            current_dir = (base_dir / rel_fp).parent
            if raw_url.startswith("/"):
                target = base_dir / raw_url[1:]
            else:
                target = (current_dir / raw_url).resolve()

            # Ensure target is still inside base_dir
            try:
                target_rel = target.relative_to(base_dir)
            except ValueError:
                # Link points outside docs/Refactor – treat as external, do not flag
                continue

            target_str = _normalize_path(str(target_rel))

            # Directory link
            if raw_url.endswith("/"):
                dir_path = base_dir / target_str
                if dir_path.is_dir():
                    has_index = any(
                        (dir_path / name).is_file()
                        for name in ("_index.md", "README.md", "00_目录与导航.md")
                    )
                    if not has_index:
                        broken[fp.relative_to(PROJECT_ROOT)].append(
                            f"[{match.group(1)}]({url}) -> missing index in directory"
                        )
                else:
                    broken[fp.relative_to(PROJECT_ROOT)].append(
                        f"[{match.group(1)}]({url}) -> directory does not exist"
                    )
                continue

            # File link
            lookup = target_str.lower()
            if lookup not in file_index:
                # Also try appending .md if not present
                if not lookup.endswith(".md") and (lookup + ".md") not in file_index:
                    broken[fp.relative_to(PROJECT_ROOT)].append(
                        f"[{match.group(1)}]({url}) -> file does not exist"
                    )

    return dict(broken)


# ---------------------------------------------------------------------------
# Check 4: Lean `sorry` Counter
# ---------------------------------------------------------------------------


def count_sorrys() -> tuple[int, list[tuple[Path, int]]]:
    counts: list[tuple[Path, int]] = []
    total = 0

    for fp in sorted(PROJECT_ROOT.rglob("*.lean")):
        try:
            content = fp.read_text(encoding="utf-8")
        except Exception:
            continue
        # Count standalone "sorry" tokens (whole word)
        n = len(re.findall(r"\bsorry\b", content))
        if n:
            rel = fp.relative_to(PROJECT_ROOT)
            counts.append((rel, n))
            total += n

    counts.sort(key=lambda x: x[1], reverse=True)
    return total, counts


# ---------------------------------------------------------------------------
# Check 5: Duplicate Directory Name Detection
# ---------------------------------------------------------------------------


def find_duplicate_dirs(base_dir: Path) -> dict[str, list[Path]]:
    dir_map: dict[str, list[Path]] = defaultdict(list)

    def walk(current: Path, rel: Path) -> None:
        for child in sorted(current.iterdir()):
            if child.is_dir():
                child_rel = rel / child.name
                dir_map[child.name].append(child_rel)
                walk(child, child_rel)

    if base_dir.exists():
        walk(base_dir, Path("."))

    duplicates = {name: paths for name, paths in dir_map.items() if len(paths) > 1}
    return duplicates


# ---------------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------------


def print_report(
    empty_flagged: list[Path],
    placeholder_flagged: list[tuple[Path, list[str]]],
    broken_links: dict[Path, list[str]],
    sorry_total: int,
    sorry_top: list[tuple[Path, int]],
    duplicate_dirs: dict[str, list[Path]],
) -> bool:
    """Print the quality gate report. Returns True if PASS, False if FAIL."""

    fail = False

    print("=" * 40)
    print("FormalScience Quality Gate")
    print("=" * 40)

    # Check 1
    if empty_flagged:
        print(f"[FAIL] Empty document check: {len(empty_flagged)} issue(s)")
        for p in empty_flagged:
            print(f"       - {p}")
        fail = True
    else:
        print("[PASS] Empty document check: 0 issues")

    # Check 2
    if placeholder_flagged:
        print(f"[FAIL] Placeholder check: {len(placeholder_flagged)} issue(s)")
        for p, _ in placeholder_flagged:
            print(f"       - {p}")
        fail = True
    else:
        print("[PASS] Placeholder check: 0 issues")

    # Check 3
    total_broken = sum(len(v) for v in broken_links.values())
    if broken_links:
        print(f"[FAIL] Broken link check: {total_broken} issue(s) in {len(broken_links)} file(s)")
        for p, links in sorted(broken_links.items()):
            for link in links:
                print(f"       - {p}: {link}")
        fail = True
    else:
        print("[PASS] Broken link check: 0 issues")

    # Check 4
    if sorry_total > 400:
        print(f"[WARN] Lean sorry count: {sorry_total} (threshold: 400)")
    else:
        print(f"[PASS] Lean sorry count: {sorry_total} (threshold: 400)")

    print("       Top 10 files by sorry count:")
    for p, n in sorry_top[:10]:
        print(f"       - {p}: {n}")

    # Check 5
    if duplicate_dirs:
        print(f"[WARN] Duplicate directories: {len(duplicate_dirs)} found")
        for name, paths in sorted(duplicate_dirs.items()):
            for path in paths:
                path_str = path.as_posix() if str(path) != "." else ""
                display = f"docs/Refactor/{path_str}" if path_str else "docs/Refactor"
                print(f"       - {display}")
    else:
        print("[PASS] Duplicate directories: 0 found")

    print("-" * 40)
    result = "FAIL" if fail else "PASS"
    print(f"Result: {result}")
    return not fail


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="FormalScience Quality Gate")
    parser.add_argument(
        "--line-threshold",
        type=int,
        default=30,
        help="Maximum line count for a file to be considered potentially empty (default: 30)",
    )
    parser.add_argument(
        "--substantive-threshold",
        type=int,
        default=5,
        help="Minimum substantive lines before a short file is flagged (default: 5)",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()

    scan_dirs = [PROJECT_ROOT / "docs" / "Refactor", PROJECT_ROOT / "Composed"]

    # 1. Empty documents
    empty_flagged = check_empty_documents(
        scan_dirs,
        line_threshold=args.line_threshold,
        substantive_threshold=args.substantive_threshold,
    )

    # 2. Placeholders
    placeholder_flagged = check_placeholders(scan_dirs)

    # 3. Broken links (docs/Refactor only)
    broken_links = check_broken_links(PROJECT_ROOT / "docs" / "Refactor")

    # 4. Lean sorrys
    sorry_total, sorry_top = count_sorrys()

    # 5. Duplicate directories
    duplicate_dirs = find_duplicate_dirs(PROJECT_ROOT / "docs" / "Refactor")

    passed = print_report(
        empty_flagged,
        placeholder_flagged,
        broken_links,
        sorry_total,
        sorry_top,
        duplicate_dirs,
    )

    return 0 if passed else 1


if __name__ == "__main__":
    sys.exit(main())
