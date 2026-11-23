#!/usr/bin/env python3
"""
Wave-15 Master Archive & Final Status Report Verification Script (M02).

Checks:
  1. 100% file:// link resolution in MASTER_ERH_RESEARCH_REPORT.md and FINAL_WAVE15_STATUS_REPORT.md.
  2. Exact filesystem counts of wave reports, Python scripts, and Lean 4.33.1 Blueprint v3 modules.
  3. Coverage check: all 19 Wave 10-15 reports and all 20 Wave 10-15 scripts are linked in both files.
  4. LaTeX `$ ... $` balance & unescaped prose `$` hygiene across both files.
  5. Banned hype-phrase regex check (0 hits required in FINAL_WAVE15_STATUS_REPORT.md and all new Wave-15 sections of MASTER_ERH_RESEARCH_REPORT.md).
  6. Structural heading check & read-only preservation check for historical FINAL_OVERNIGHT_SUMMARY.md.
"""

from pathlib import Path
import re
import sys
from urllib.parse import unquote

ROOT = Path("/Users/tiancaikeyize/Downloads/阅读黎曼猜想证明")
ERH = ROOT / "erh_research"
MASTER_MD = ERH / "MASTER_ERH_RESEARCH_REPORT.md"
FINAL_W15_MD = ERH / "FINAL_WAVE15_STATUS_REPORT.md"
HIST_W9_MD = ERH / "FINAL_OVERNIGHT_SUMMARY.md"

LINK_RE = re.compile(r"\[[^\]]*\]\((file://[^)\s]+)\)")
BANNED_HYPE = [
    "重磅",
    "震撼",
    "历史性",
    "100%无条件",
    "100% 无条件",
    "彻底解决",
    "彻底消除",
    "终极突破",
    "完美闭环",
    "史诗级",
    "全面攻克",
    "里程碑式",
]


def check_links(md_path: Path) -> tuple[int, list[tuple[int, str, str]]]:
    text = md_path.read_text(encoding="utf-8")
    total = 0
    broken: list[tuple[int, str, str]] = []
    for lineno, line in enumerate(text.splitlines(), 1):
        for match in LINK_RE.finditer(line):
            url = match.group(1)
            total += 1
            raw_path = url[len("file://") :]
            if "#" in raw_path:
                raw_path = raw_path.split("#", 1)[0]
            decoded = unquote(raw_path)
            if not Path(decoded).exists():
                broken.append((lineno, url, decoded))
    return total, broken


def check_dollar_hygiene(md_path: Path) -> list[tuple[int, str]]:
    """Check balanced `$ ... $` and `$$ ... $$` on non-code lines."""
    text = md_path.read_text(encoding="utf-8")
    issues: list[tuple[int, str]] = []
    in_fence = False
    in_display_math = False

    for lineno, line in enumerate(text.splitlines(), 1):
        stripped = line.strip()
        if stripped.startswith("```"):
            in_fence = not in_fence
            continue
        if in_fence:
            continue

        # Remove inline code spans `...`
        cleaned = re.sub(r"`[^`]*`", "", line)
        # Remove escaped \$
        cleaned = cleaned.replace(r"\$", "")

        # Handle pure display math delimiters `$$` on a line
        if cleaned.strip() == "$$":
            in_display_math = not in_display_math
            continue

        # Count occurrences of `$$`
        dd_count = cleaned.count("$$")
        if dd_count % 2 == 1:
            in_display_math = not in_display_math
        cleaned_no_dd = cleaned.replace("$$", "")

        if in_display_math:
            continue

        single_dollars = cleaned_no_dd.count("$")
        if single_dollars % 2 != 0:
            issues.append((lineno, f"Odd number of unescaped `$` ({single_dollars}): {line[:120]}"))

    if in_display_math:
        issues.append((0, "Unclosed display math `$$` block at EOF"))
    return issues


def scan_hype(text: str, line_offset: int = 0) -> list[tuple[int, str, str]]:
    hits: list[tuple[int, str, str]] = []
    for idx, line in enumerate(text.splitlines(), 1 + line_offset):
        for word in BANNED_HYPE:
            if word in line:
                hits.append((idx, word, line.strip()[:120]))
    return hits


def main() -> int:
    errors: list[str] = []
    print("=== Wave-15 Master Archive Verification (M02) ===\n")

    # 1. Exact filesystem counts
    wave_dirs = ["reports"] + [f"wave{i}" for i in range(3, 16)]
    per_dir_counts: dict[str, int] = {}
    for d in wave_dirs:
        p = ERH / d
        per_dir_counts[d] = len(list(p.glob("*.md"))) if p.exists() else 0
    total_wave_reports = sum(per_dir_counts.values())
    top_level_mds = sorted(p.name for p in ERH.glob("*.md"))
    milestone_reports = [
        name for name in top_level_mds if name in ("FINAL_OVERNIGHT_SUMMARY.md", "FINAL_WAVE15_STATUS_REPORT.md")
    ]
    total_task_reports = total_wave_reports + len(milestone_reports)
    total_all_mds = total_wave_reports + len(top_level_mds)

    core_w10_15_reports = [
        "wave10/H01_regime_b_fgauge_nygaard_effective.md",
        "wave10/H02_tame_nonabelian_liftk_and_syn_scaling.md",
        "wave10/H03_prove_lst56_infinite_s3_mu2.md",
        "wave10/H04_rq_count1_unconditional_lds_and_torsion.md",
        "wave10/H05_hostex_weakest_threshold_and_gs_tower.md",
        "wave10/H06_brumer_stark_maass_and_block_gsp4.md",
        "wave10/H07_general_real_quadratic_d4q8_closure.md",
        "wave10/H08_higher_deg_eisenstein_mu_cancellation.md",
        "wave11/I01_close_lst_sieve_infinite_s3.md",
        "wave11/I02_integral_finite_jet_and_denominators_a2.md",
        "wave11/I03_audit_wave10_theorems.md",
        "wave12/J01_phi_compat_ode_cartier_regime_b.md",
        "wave12/J02_audit_i01_and_i02.md",
        "wave13/K01_audit_j01_universal_h2syn_bound.md",
        "wave13/K02_item8_full_ch23_closure_and_linear_bridge.md",
        "wave14/L01_prove_or_refute_k02_q1.md",
        "wave14/L02_crystalline_sen_bound_q1.md",
        "wave14/L03_audit_k02_linear_bridge_and_ch23.md",
        "wave15/M01_audit_l02_l01_item8_closure.md",
    ]
    core_w10_15_scripts = [
        "verify_h01_fgauge_nygaard.py",
        "verify_h02_tame_liftk_and_syn_snf.py",
        "verify_h03_lst56_euler_products.py",
        "verify_h04_lds_mglob.py",
        "verify_h05_hostex_gs_threshold.py",
        "verify_h06_block_gsp4_and_bs.py",
        "verify_h07_general_k0_d4q8.py",
        "verify_h08_eisenstein_mu_cancel.py",
        "verify_i01_lst_sieve.py",
        "verify_i02_finite_jet_a2.py",
        "verify_i03_audit_wave10.py",
        "verify_j01_phi_compat_a2.py",
        "verify_j02_audit_i01_i02.py",
        "verify_k01_audit_j01.py",
        "verify_k02_item8_ch23_closure.py",
        "verify_l01_k02_q1.py",
        "verify_l02_crystalline_q1.py",
        "verify_l03_audit_k02.py",
        "verify_m01_audit_l02_l01.py",
        "verify_lean_blueprint_v4.py",
        "verify_wave15_master_archive.py",
    ]
    w15_lean_v4 = [
        "Item8_FullClosure_J01_K02_L02.lean",
        "GeneralRealQuad_D4Q8_H07_H05.lean",
        "InfiniteS3_Mu2Zero_H03_I01.lean",
    ]

    w10_15_reports = sorted(
        f"{d}/{p.name}"
        for d in [f"wave{i}" for i in range(10, 16)]
        for p in (ERH / d).glob("*.md")
    )
    py_scripts = sorted((ERH / "scripts").glob("*.py"))
    w10_15_scripts = sorted(
        p.name
        for p in py_scripts
        if p.name.startswith(
            ("verify_h", "verify_i", "verify_j", "verify_k", "verify_l", "verify_m", "verify_wave15", "verify_lean_blueprint_v4")
        )
    )
    lean_files = sorted((ERH / "lean_erh_blueprint").glob("*.lean"))
    lean_lines = sum(len(p.read_text(encoding="utf-8").splitlines()) for p in lean_files)

    print("[1] Filesystem Inventory:")
    print("  Per-wave markdown counts:", per_dir_counts)
    print(f"  Individual wave reports (W1-15) : {total_wave_reports}")
    print(f"  Milestone status reports        : {len(milestone_reports)} {milestone_reports}")
    print(f"  Total completed task reports    : {total_task_reports}")
    print(f"  Total .md files in erh_research : {total_all_mds} (incl. MASTER_ERH_RESEARCH_REPORT.md)")
    print(f"  Wave 10-15 individual reports   : {len(w10_15_reports)}")
    print(f"  Total Python scripts            : {len(py_scripts)} (Wave 10-15: {len(w10_15_scripts)})")
    print(f"  Lean Blueprint (v3 + v4)        : {len(lean_files)} modules, {lean_lines} lines")

    if total_wave_reports < 118:
        errors.append(f"Expected >= 118 individual wave reports, found {total_wave_reports}")
    if total_task_reports < 120:
        errors.append(f"Expected >= 120 total task reports, found {total_task_reports}")
    if len(py_scripts) < 105:
        errors.append(f"Expected >= 105 Python scripts, found {len(py_scripts)}")
    if len(lean_files) < 14 or lean_lines < 5762:
        errors.append(f"Expected >= 14 Lean modules / >= 5762 lines, found {len(lean_files)} / {lean_lines}")

    # 2. Link checks
    print("\n[2] File:// Link Resolution:")
    for label, path in [("MASTER_ERH_RESEARCH_REPORT.md", MASTER_MD), ("FINAL_WAVE15_STATUS_REPORT.md", FINAL_W15_MD)]:
        total_links, broken_links = check_links(path)
        print(f"  {label}: {total_links} links checked, {len(broken_links)} broken")
        for lineno, url, decoded in broken_links:
            errors.append(f"Broken link in {label}:{lineno} -> {decoded}")

    # 3. Coverage of all Wave 10-15 core reports, scripts, and Lean v4 modules in both files
    print("\n[3] Wave 10-15 Artifact Coverage:")
    for label, path in [("MASTER_ERH_RESEARCH_REPORT.md", MASTER_MD), ("FINAL_WAVE15_STATUS_REPORT.md", FINAL_W15_MD)]:
        txt = path.read_text(encoding="utf-8")
        missing_rep = [r for r in core_w10_15_reports if r not in txt]
        missing_scr = [s for s in core_w10_15_scripts if s not in txt]
        missing_lean = [m for m in w15_lean_v4 if m not in txt]
        print(
            f"  {label}: core reports {len(core_w10_15_reports) - len(missing_rep)}/{len(core_w10_15_reports)}, "
            f"scripts {len(core_w10_15_scripts) - len(missing_scr)}/{len(core_w10_15_scripts)}, "
            f"Lean v4 modules {len(w15_lean_v4) - len(missing_lean)}/{len(w15_lean_v4)}"
        )
        if missing_rep:
            errors.append(f"{label} missing Wave 10-15 report links: {missing_rep}")
        if missing_scr:
            errors.append(f"{label} missing Wave 10-15 script links: {missing_scr}")
        if missing_lean:
            errors.append(f"{label} missing Wave 15 Lean v4 links: {missing_lean}")

    # 4. Dollar / LaTeX hygiene
    print("\n[4] LaTeX `$ ... $` & Prose Dollar Hygiene:")
    for label, path in [("MASTER_ERH_RESEARCH_REPORT.md", MASTER_MD), ("FINAL_WAVE15_STATUS_REPORT.md", FINAL_W15_MD)]:
        d_issues = check_dollar_hygiene(path)
        print(f"  {label}: {len(d_issues)} issue(s)")
        for lineno, msg in d_issues:
            errors.append(f"Dollar hygiene in {label}:{lineno}: {msg}")

    # 5. Banned hype-phrase hygiene
    print("\n[5] Banned Hype-Phrase Check:")
    final_txt = FINAL_W15_MD.read_text(encoding="utf-8")
    final_hype = scan_hype(final_txt)
    print(f"  FINAL_WAVE15_STATUS_REPORT.md (full): {len(final_hype)} hit(s)")
    for lineno, word, snippet in final_hype:
        errors.append(f"Banned hype word `{word}` in FINAL_WAVE15_STATUS_REPORT.md:{lineno}: {snippet}")

    master_lines = MASTER_MD.read_text(encoding="utf-8").splitlines()
    # Identify boundary of Wave-15 new top dashboard (before `## 0. 阅读须知`) and new tail (from `## 18.`)
    idx_hist_start = next((i for i, l in enumerate(master_lines) if l.startswith("## 0. 阅读须知")), None)
    idx_w15_tail = next((i for i, l in enumerate(master_lines) if l.startswith("## 18. Wave 10")), None)
    if idx_hist_start is None or idx_w15_tail is None:
        errors.append("Could not locate expected section boundaries in MASTER_ERH_RESEARCH_REPORT.md")
    else:
        top_new_txt = "\n".join(master_lines[:idx_hist_start])
        tail_new_txt = "\n".join(master_lines[idx_w15_tail:])
        top_hits = scan_hype(top_new_txt, line_offset=0)
        tail_hits = scan_hype(tail_new_txt, line_offset=idx_w15_tail)
        hist_txt = "\n".join(master_lines[idx_hist_start:idx_w15_tail])
        hist_hits = scan_hype(hist_txt, line_offset=idx_hist_start)
        print(f"  MASTER_ERH_RESEARCH_REPORT.md (new Wave-15 top + §18-§22): {len(top_hits) + len(tail_hits)} hit(s)")
        print(f"  MASTER_ERH_RESEARCH_REPORT.md (untouched historical §0-§17): {len(hist_hits)} historical hit(s) (read-only preserved)")
        for lineno, word, snippet in top_hits + tail_hits:
            errors.append(f"Banned hype word `{word}` in MASTER new text L{lineno}: {snippet}")

    # 6. Structural headings & historical FINAL_OVERNIGHT_SUMMARY.md read-only check
    print("\n[6] Structural & Read-Only Checks:")
    master_txt = MASTER_MD.read_text(encoding="utf-8")
    required_master_headings = [
        "## §0 顶部执行仪表盘",
        "## 0. 阅读须知（请先读）",
        "## 17. 最新 8 项终极状态总表",
        "## 18. Wave 10",
        "## 19. Wave 11",
        "## 20. Waves 12–15",
        "## 21. 总勘误表与已封死路线登记簿",
        "## 22. Wave-15 终极前沿地图与 4 项可独立发表的主定理",
    ]
    missing_h = [h for h in required_master_headings if h not in master_txt]
    print(f"  MASTER required headings present: {len(required_master_headings) - len(missing_h)}/{len(required_master_headings)}")
    if missing_h:
        errors.append(f"Missing headings in MASTER: {missing_h}")

    hist_lines = HIST_W9_MD.read_text(encoding="utf-8").splitlines()
    l125_ok = len(hist_lines) >= 125 and "Regime A" in hist_lines[124]
    print(f"  Historical FINAL_OVERNIGHT_SUMMARY.md intact (lines={len(hist_lines)}, L125 preserved={l125_ok})")
    if not l125_ok:
        errors.append("Historical FINAL_OVERNIGHT_SUMMARY.md line 125 unexpectedly altered")

    print("\n=== SUMMARY ===")
    if errors:
        print(f"FAILED with {len(errors)} error(s):")
        for e in errors:
            print("  -", e)
        return 1
    print("ALL CHECKS PASSED (0 errors, 100% links valid, 0 hype hits in new text).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
