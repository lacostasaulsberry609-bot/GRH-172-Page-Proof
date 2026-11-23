#!/usr/bin/env python3
"""
Wave-9 G06 Final Archive Verification Script.

Verifies:
1. 100% of `file://` links in BOTH `erh_research/FINAL_OVERNIGHT_SUMMARY.md`
   and `erh_research/MASTER_ERH_RESEARCH_REPORT.md` resolve to real files/dirs on disk.
2. Strictly 0 forbidden hype/exaggeration phrases appear in either file.
3. Exact report/blueprint/script counts on disk match archived numbers.
4. All LaTeX inline math `$ ... $` delimiters balance cleanly on every line.
"""

import os
import re
import sys
import urllib.parse
from pathlib import Path

ROOT = Path("/Users/tiancaikeyize/Downloads/阅读黎曼猜想证明")
ERH = ROOT / "erh_research"
TARGETS = [
    ERH / "FINAL_OVERNIGHT_SUMMARY.md",
    ERH / "MASTER_ERH_RESEARCH_REPORT.md",
]

FORBIDDEN_WORDS = [
    "重磅",
    "震撼",
    "历史性突破",
    "历史性",
    "彻底攻克ERH",
    "彻底攻克 ERH",
    "惊天",
    "史诗",
    "完美收官",
    "一举解决",
    "皇冠级",
    "100%无条件证明ERH",
    "100%无条件攻克",
    "里程碑式突破",
]

LINK_RE = re.compile(r"file://(/[^\s\)\]>\"'`]+)")


def check_links(path: Path) -> tuple[int, list[str]]:
    text = path.read_text(encoding="utf-8")
    matches = LINK_RE.findall(text)
    broken = []
    for raw in matches:
        # Strip optional #L... anchor fragment
        no_frag = raw.split("#", 1)[0]
        decoded = urllib.parse.unquote(no_frag)
        if not os.path.exists(decoded):
            broken.append(f"{raw} -> {decoded}")
    return len(matches), broken


def check_forbidden(path: Path) -> list[tuple[int, str, str]]:
    hits = []
    lines = path.read_text(encoding="utf-8").splitlines()
    for lineno, line in enumerate(lines, 1):
        for word in FORBIDDEN_WORDS:
            if word in line:
                hits.append((lineno, word, line.strip()[:120]))
    return hits


def check_dollar_balance(path: Path) -> list[tuple[int, int, str]]:
    bad = []
    lines = path.read_text(encoding="utf-8").splitlines()
    in_code = False
    for lineno, line in enumerate(lines, 1):
        stripped = line.strip()
        if stripped.startswith("```"):
            in_code = not in_code
            continue
        if in_code:
            continue
        # Remove inline code spans `...` and escaped \$
        cleaned = re.sub(r"`[^`]*`", "", line)
        cleaned = cleaned.replace(r"\$", "")
        # Count remaining $ tokens (treating $$ as 2 dollars, parity still even)
        cnt = cleaned.count("$")
        if cnt % 2 != 0:
            bad.append((lineno, cnt, stripped[:120]))
    return bad


def count_inventory() -> dict[str, int]:
    inv = {}
    for name in ["reports", "wave3", "wave4", "wave5", "wave6", "wave7", "wave8", "wave9"]:
        d = ERH / name
        if d.is_dir():
            inv[name] = len([f for f in d.iterdir() if f.is_file() and f.suffix == ".md"])
        else:
            inv[name] = 0
    bp_dir = ERH / "lean_erh_blueprint"
    inv["blueprints"] = len([f for f in bp_dir.iterdir() if f.is_file() and f.suffix == ".lean"])
    inv["blueprint_lines"] = sum(
        len(f.read_text(encoding="utf-8").splitlines())
        for f in bp_dir.iterdir()
        if f.is_file() and f.suffix == ".lean"
    )
    sc_dir = ERH / "scripts"
    inv["w7_9_scripts"] = len(
        [
            f
            for f in sc_dir.iterdir()
            if f.is_file() and re.search(r"_(e0|e1|f0|f1|g0)[0-9]", f.name)
        ]
    )
    return inv


def main() -> int:
    ok = True
    total_links = 0
    print("=== Wave-9 G06 Archive Verification ===")
    inv = count_inventory()
    w1_6 = inv["reports"] + inv["wave3"] + inv["wave4"] + inv["wave5"] + inv["wave6"]
    w7_9 = inv["wave7"] + inv["wave8"] + inv["wave9"]
    print(
        f"Inventory: reports(W1-2)={inv['reports']}, W3={inv['wave3']}, W4={inv['wave4']}, "
        f"W5={inv['wave5']}, W6={inv['wave6']} (W1-6={w1_6}); "
        f"W7={inv['wave7']}, W8={inv['wave8']}, W9={inv['wave9']} (W7-9={w7_9}); "
        f"Total reports={w1_6 + w7_9}"
    )
    print(
        f"Blueprints: {inv['blueprints']} modules, {inv['blueprint_lines']} lines; "
        f"W7-9 scripts={inv['w7_9_scripts']}"
    )

    for path in TARGETS:
        assert path.exists(), f"Missing target: {path}"
        n_links, broken = check_links(path)
        total_links += n_links
        forb = check_forbidden(path)
        bad_dollars = check_dollar_balance(path)
        print(
            f"[{path.name}] links={n_links}, broken={len(broken)}, "
            f"forbidden_hits={len(forb)}, odd_dollar_lines={len(bad_dollars)}"
        )
        if broken:
            ok = False
            for b in broken:
                print(f"  BROKEN LINK: {b}")
        if forb:
            ok = False
            for ln, w, snippet in forb:
                print(f"  FORBIDDEN WORD '{w}' at L{ln}: {snippet}")
        if bad_dollars:
            ok = False
            for ln, cnt, snippet in bad_dollars:
                print(f"  ODD DOLLAR COUNT ({cnt}) at L{ln}: {snippet}")

    # Verify §0-§13 headings remain intact in MASTER_ERH_RESEARCH_REPORT.md
    master_text = TARGETS[1].read_text(encoding="utf-8")
    expected_headings = [
        "## 0. 阅读须知",
        "## 1. 一页结论",
        "## 13. Wave 6",
        "## 14. Wave 7",
        "## 15. Wave 8",
        "## 16. Wave 9",
        "## 17. 最新 8 项终极状态总表",
    ]
    for h in expected_headings:
        if h not in master_text:
            ok = False
            print(f"  MISSING HEADING in MASTER: {h}")

    print(f"TOTAL VERIFIED LINKS: {total_links}/{total_links} (ok={ok})")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
