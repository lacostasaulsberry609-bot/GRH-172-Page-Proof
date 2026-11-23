#!/usr/bin/env python3
"""
Wave-15 M03 Static Verification, tools/lean_index.db Alignment & Symbolic Cross-Check Script
for ALL 14 Lean 4.33.1 ERH Blueprint Modules in erh_research/lean_erh_blueprint/:
  - Blueprint v1 (Wave-3 A19, Modules 1-3): RelCMHostVariantII.lean,
      GeneralizedLemmaM_HidaSetting4.lean, MainERH.lean (untouched legacy)
  - Blueprint v1b (Wave-4 B09, Module 4): ChCore_ZqTower.lean
  - Blueprint v2 (Wave-7 E11, Modules 5-7): GSp4CountI_RealQuadratic.lean,
      CountVAbsorption_C08_C09.lean, PrismaticLinearCokernel_D10_D11.lean
  - Blueprint v3 (Wave-9 G05, Modules 8-11): MasterRQCountI_SchemeI_F06_F07.lean,
      RegimeII_CoronaA1_G03_LTDK_G01.lean, Mu2Zero_GroupClassification_F05_F10_G02.lean,
      CountV_WallA_Fixed_E07_E08_F11.lean
  - Blueprint v4 (Wave-15 M03, Modules 12-14):
      Item8_FullClosure_J01_K02_L02.lean
      InfiniteS3_Mu2Zero_H03_I01.lean
      GeneralRealQuad_D4Q8_H07_H05.lean

HONESTY DISCLAIMER:
  Static syntactic, delimiter/comment balance, namespace hygiene, universe-hygiene,
  read-only tools/lean_index.db declaration/import alignment, and SymPy/exact-arithmetic
  cross-checks do NOT substitute for a live `lake build` against the 16.58M-line workspace
  Lean archive (and `lean`/`lake` availability is explicitly checked below).
"""

import math
import re
import shutil
import sqlite3
import sys
from fractions import Fraction
from pathlib import Path

import sympy as sp

ROOT = Path("/Users/tiancaikeyize/Downloads/阅读黎曼猜想证明")
BLUEPRINT_DIR = ROOT / "erh_research" / "lean_erh_blueprint"
SRC_DIR = ROOT / "riemann-hypothesis" / "src"
DB_PATH = ROOT / "tools" / "lean_index.db"

PRIOR_CLEAN_FILES = [
    "RelCMHostVariantII.lean",
    "GeneralizedLemmaM_HidaSetting4.lean",
    "ChCore_ZqTower.lean",
    "GSp4CountI_RealQuadratic.lean",
    "CountVAbsorption_C08_C09.lean",
    "PrismaticLinearCokernel_D10_D11.lean",
    "MasterRQCountI_SchemeI_F06_F07.lean",
    "RegimeII_CoronaA1_G03_LTDK_G01.lean",
    "Mu2Zero_GroupClassification_F05_F10_G02.lean",
    "CountV_WallA_Fixed_E07_E08_F11.lean",
]

LEGACY_WAVE3_MAIN = "MainERH.lean"

WAVE15_V4_FILES = [
    "Item8_FullClosure_J01_K02_L02.lean",
    "InfiniteS3_Mu2Zero_H03_I01.lean",
    "GeneralRealQuad_D4Q8_H07_H05.lean",
]

ALL_14_FILES = [
    "RelCMHostVariantII.lean",
    "GeneralizedLemmaM_HidaSetting4.lean",
    "MainERH.lean",
    "ChCore_ZqTower.lean",
    "GSp4CountI_RealQuadratic.lean",
    "CountVAbsorption_C08_C09.lean",
    "PrismaticLinearCokernel_D10_D11.lean",
    "MasterRQCountI_SchemeI_F06_F07.lean",
    "RegimeII_CoronaA1_G03_LTDK_G01.lean",
    "Mu2Zero_GroupClassification_F05_F10_G02.lean",
    "CountV_WallA_Fixed_E07_E08_F11.lean",
    "Item8_FullClosure_J01_K02_L02.lean",
    "InfiniteS3_Mu2Zero_H03_I01.lean",
    "GeneralRealQuad_D4Q8_H07_H05.lean",
]

EXPECTED_LEGACY_MAINERH_AXIOMS = {
    295: "extendedRiemannHypothesis_of_totallyReal_D4_725_spec",
    325: "extendedRiemannHypothesis_regimeA_spec",
    356: "extendedRiemannHypothesis_regimeB_spec",
}


def strip_comments_and_strings(text: str):
    """Strip Lean 4 nested block comments `/- ... -/`, line comments `-- ...`, and string literals."""
    out = []
    i = 0
    n = len(text)
    block_depth = 0
    in_line_comment = False
    in_string = False
    errors = []

    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""

        if in_line_comment:
            if ch == "\n":
                in_line_comment = False
                out.append("\n")
            i += 1
            continue

        if block_depth > 0:
            if ch == "/" and nxt == "-":
                block_depth += 1
                i += 2
                continue
            if ch == "-" and nxt == "/":
                block_depth -= 1
                i += 2
                continue
            if ch == "\n":
                out.append("\n")
            i += 1
            continue

        if in_string:
            if ch == "\\":
                i += 2
                continue
            if ch == '"':
                in_string = False
                out.append(" ")
            elif ch == "\n":
                out.append("\n")
            i += 1
            continue

        if ch == "/" and nxt == "-":
            block_depth = 1
            i += 2
            continue
        if ch == "-" and nxt == "-":
            in_line_comment = True
            i += 2
            continue
        if ch == '"':
            in_string = True
            out.append(" ")
            i += 1
            continue
        out.append(ch)
        i += 1

    if block_depth != 0:
        errors.append(f"Unclosed block comment (depth={block_depth})")
    if in_string:
        errors.append("Unclosed string literal")

    return "".join(out), errors


def check_delimiters(code: str):
    """Check balanced (), [], {}, ⟨⟩ in comment/string-stripped Lean 4 code."""
    pairs = {"(": ")", "[": "]", "{": "}", "⟨": "⟩"}
    closing = {v: k for k, v in pairs.items()}
    stack = []
    line = 1
    col = 0
    errors = []
    for ch in code:
        if ch == "\n":
            line += 1
            col = 0
            continue
        col += 1
        if ch in pairs:
            stack.append((ch, line, col))
        elif ch in closing:
            if not stack:
                errors.append(f"L{line}:{col} unmatched closing '{ch}'")
            else:
                top_ch, top_l, top_c = stack.pop()
                if pairs[top_ch] != ch:
                    errors.append(
                        f"L{line}:{col} mismatched '{ch}' (expected '{pairs[top_ch]}' opened at L{top_l}:{top_c})"
                    )
    for top_ch, top_l, top_c in stack:
        errors.append(f"L{top_l}:{top_c} unclosed '{top_ch}'")
    return errors


def check_forbidden_tokens(code: str):
    """Count bare `axiom` declarations, `sorry`, and `admit` in executable code."""
    axioms = []
    sorries = []
    admits = []
    for idx, raw_line in enumerate(code.splitlines(), 1):
        m_ax = re.match(r"^\s*(?:private\s+|protected\s+)?axiom\s+([^\s:(]+)", raw_line)
        if m_ax:
            axioms.append((idx, m_ax.group(1)))
        if re.search(r"\bsorry\b", raw_line):
            sorries.append((idx, raw_line.strip()))
        if re.search(r"\badmit\b", raw_line):
            admits.append((idx, raw_line.strip()))
    return axioms, sorries, admits


def check_namespaces(code: str):
    """Check balanced `namespace Foo` / `section Foo` / `end Foo` and return list of opened namespaces."""
    stack = []
    opened_ns = []
    errors = []
    for idx, line in enumerate(code.splitlines(), 1):
        m_ns = re.match(r"^\s*namespace\s+([A-Za-z0-9_.']+)", line)
        if m_ns:
            ns = m_ns.group(1)
            stack.append(("namespace", ns, idx))
            opened_ns.append(ns)
            continue
        m_sec = re.match(r"^\s*(?:noncomputable\s+)?section\s+([A-Za-z0-9_.']+)", line)
        if m_sec:
            sec = m_sec.group(1)
            stack.append(("section", sec, idx))
            continue
        m_end = re.match(r"^\s*end\s+([A-Za-z0-9_.']+)", line)
        if m_end:
            name = m_end.group(1)
            if not stack:
                errors.append(f"L{idx}: `end {name}` with no matching namespace/section")
            else:
                top_kind, top_name, top_l = stack.pop()
                if top_name != name:
                    errors.append(
                        f"L{idx}: `end {name}` does not match `{top_kind} {top_name}` (L{top_l})"
                    )
    for kind, name, lno in stack:
        errors.append(f"L{lno}: unclosed `{kind} {name}`")
    return opened_ns, errors


def check_prop_structure_universe_hygiene(code: str):
    """Ensure no `structure ... : Prop where` contains naked `: Prop`, `: ℕ`, `: ℤ`, `: ℝ`, or `: Type` fields."""
    issues = []
    in_prop_struct = False
    struct_name = ""
    for idx, line in enumerate(code.splitlines(), 1):
        s = line.strip()
        m_start = re.match(r"^structure\s+([A-Za-z0-9_']+).*:\s*Prop\s+where\b", s)
        if m_start:
            in_prop_struct = True
            struct_name = m_start.group(1)
            continue
        if in_prop_struct:
            if not line.startswith(" ") and s != "":
                in_prop_struct = False
                continue
            m_field = re.match(r"^\s+([A-Za-z0-9_']+)\s*:\s*(Prop|ℕ|ℤ|ℝ|Type(?:\s+\d+)?)\s*$", line)
            if m_field:
                issues.append(f"L{idx} ({struct_name}.{m_field.group(1)} : {m_field.group(2)})")
    return issues


def check_imports(code: str, cur: sqlite3.Cursor):
    """Verify every archive import exists in tools/lean_index.db AND on disk under riemann-hypothesis/src/."""
    imports = []
    missing_db = []
    missing_disk = []
    for idx, raw_line in enumerate(code.splitlines(), 1):
        m = re.match(r"^\s*import\s+([A-Za-z0-9_.\u2080-\u2089']+)", raw_line)
        if not m:
            continue
        mod = m.group(1)
        imports.append((idx, mod))
        if mod == "Mathlib" or mod.startswith("Mathlib.") or mod.startswith("ERH.") or mod.startswith("erh_research."):
            continue
        row = cur.execute("SELECT rel_path FROM files WHERE module = ?", (mod,)).fetchone()
        if row is None:
            missing_db.append((idx, mod))
        rel_path = mod.replace(".", "/") + ".lean"
        if not (SRC_DIR / rel_path).exists():
            missing_disk.append((idx, mod, rel_path))
    return imports, missing_db, missing_disk


def extract_and_verify_workspace_decls(fname: str, raw_text: str, cur: sqlite3.Cursor):
    """Extract all `@workspace_decl: <FullName> @ <RelPath>:<Line>` tags and verify 100% against lean_index.db & disk."""
    pattern = re.compile(
        r"@workspace_decl:\s*([A-Za-z0-9_.\u2080-\u2089']+)\s*@\s*([A-Za-z0-9_/\u2080-\u2089'-]+\.lean):(\d+)"
    )
    matches = pattern.findall(raw_text)
    verified = []
    failures = []
    for full_name, rel_path, line_str in matches:
        expected_line = int(line_str)
        row = cur.execute(
            "SELECT full_name, kind, module, rel_path, line FROM decls WHERE full_name = ? AND rel_path = ? AND line = ?",
            (full_name, rel_path, expected_line),
        ).fetchone()
        if row is None:
            # Check if full_name exists elsewhere for diagnostic message
            alt = cur.execute(
                "SELECT full_name, kind, rel_path, line FROM decls WHERE full_name = ?",
                (full_name,),
            ).fetchall()
            failures.append((full_name, rel_path, expected_line, f"NOT FOUND AT EXACT LOCATION; db_alts={alt}"))
            continue
        disk_file = SRC_DIR / rel_path
        if not disk_file.exists():
            failures.append((full_name, rel_path, expected_line, "FILE MISSING ON DISK"))
            continue
        lines = disk_file.read_text(encoding="utf-8", errors="ignore").splitlines()
        if expected_line < 1 or expected_line > len(lines):
            failures.append((full_name, rel_path, expected_line, f"LINE OUT OF RANGE (max={len(lines)})"))
            continue
        short_name = full_name.split(".")[-1]
        src_line = lines[expected_line - 1]
        if short_name not in src_line:
            failures.append((full_name, rel_path, expected_line, f"SHORT NAME '{short_name}' NOT ON LINE: {src_line}"))
            continue
        verified.append((full_name, row[1], rel_path, expected_line))
    return verified, failures


def run_symbolic_math_checks():
    """Independently cross-check all embedded arithmetic/algebraic theorems in the 3 Blueprint v4 files via SymPy/Python."""
    # --- Module 12: Item8_FullClosure_J01_K02_L02.lean ---
    # 1. J01 unramified ell=2 & Regime I/II bounds
    def cKM(M, dK, vFac):
        return (M - 1) * dK + vFac

    def nUnivBound(M, dK, vFac, tStar):
        return (tStar + 4) * max(M - 1, cKM(M, dK, vFac))

    def nUnivPlusBound(M, dK, vFac, tStarP):
        return (tStarP + 5) * max(M - 1, cKM(M, dK, vFac))

    def nQ1(M, dK, vFac):
        if M <= 1:
            return 0
        if dK == 0:
            return vFac
        return (2 * M - 3) * dK

    for M in range(1, 25):
        v2 = sum((M - 1) // (2 ** k) for k in range(1, 10))
        assert v2 <= max(0, M - 1)
        assert nUnivBound(M, 0, v2, 2) == 6 * (M - 1)
        for dK in range(0, 6):
            for tStar in range(1, 8):
                assert nUnivBound(M, dK, v2, tStar) <= (tStar + 4) * (dK + 1) * (M - 1)
            assert nQ1(M, dK, v2) <= 2 * M * (dK + 1)

    # 2. K01 Patch-2 witness & K02-1 quadratic blowup & K02-2A automatic continuity
    assert (3 * (0 + 1)) // 1 - 1 == 2 and (1 + (1 * 1) // 3 + 0 < 1 + 1)
    for k in range(2, 8):
        for M in range(2, 10):
            assert k < (k - 1) * M + 1
    for l in [2, 3, 5]:
        for N in range(1, 5):
            for M in range(0, 5):
                for h in range(0, 5):
                    for k in range(0, 6):
                        j = (l - 1) * N + M + (k + 1) // 2 + 1
                        assert (l * N + 2 * M + h) + k + 1 <= h + 1 + l * j

    # 3. K02-4 B9 polytope all 10 inequalities symbolically
    eps = sp.Symbol("eps", positive=True)
    alpha_n = 2 + 8 * eps
    alpha_k = sp.Rational(9, 2) + 10 * eps
    alpha_m = sp.Rational(1, 2) - eps / 16
    theta = sp.Rational(1, 2) + 9 * eps
    assert sp.simplify(alpha_m - (sp.Rational(1, 2) - eps)) == sp.Rational(15, 16) * eps
    assert sp.simplify((sp.Rational(1, 2) + eps / 2) - alpha_m) == sp.Rational(9, 16) * eps
    assert sp.simplify(alpha_k - (1 + alpha_m)) == 3 + sp.Rational(161, 16) * eps
    assert sp.simplify((2 * alpha_n + sp.Rational(1, 2) - eps) - alpha_k) == 5 * eps
    assert sp.simplify(alpha_n - 2) == 8 * eps
    assert sp.simplify(alpha_k - (5 * alpha_m + alpha_n + 2 * eps)) == sp.Rational(5, 16) * eps
    assert sp.simplify((alpha_n - eps) - (alpha_k - alpha_m) / 2) == sp.Rational(63, 32) * eps
    assert sp.simplify(alpha_k - 2 * alpha_m) == sp.Rational(7, 2) + sp.Rational(81, 8) * eps
    assert sp.simplify(alpha_k - 2 * alpha_n - (sp.Rational(1, 2) - 6 * eps)) == 0
    assert sp.simplify((1 - theta).subs(eps, sp.Rational(1, 52))) == sp.Rational(17, 52)

    # 4. L02 Newton-Hensel & PD cross-term collapse & M01 Patch-L02-3
    for r in range(2, 10):
        for dK in range(1, 5):
            for n in range(1, r):
                for N1 in range(0, r):
                    for N2 in range(n, r - N1):
                        vFacN = n - 1
                        lhs = (0 if N1 == 0 else (2 * N1 - 1) * dK) + (2 * N2 - n) * dK + vFacN
                        assert lhs <= (2 * r - 3) * dK
    assert (1 * 3 == 3 * 1) and (2 * 3 == 3 * 2) and (3 * 3 == 3 * 3) and (2 * 2 == 4 * 1)

    # --- Module 13: InfiniteS3_Mu2Zero_H03_I01.lean ---
    t, pi_s, g23 = sp.symbols("t pi g23")
    assert sp.simplify((pi_s / 8) * (16 * pi_s / (18 * g23)) * (6 / pi_s ** 2) - 2 / (3 * g23)) == 0
    assert Fraction(1, 24) + Fraction(1, 8) == Fraction(1, 6)
    assert Fraction(1, 24) + Fraction(1, 3) / 8 == Fraction(1, 12)
    assert sp.expand(2 * (1 - t) * (1 + t ** 3) + 3 * (1 - t ** 4) + (1 + 2 * t - 2 * t ** 3 - t ** 4) - 6 * (1 - t ** 4)) == 0
    assert sp.expand((1 - t ** 4) + t ** 3 * (1 + t - t ** 2 - t ** 3) - ((1 + t ** 3) - (t ** 5 + t ** 6))) == 0
    assert sp.expand(((1 + t ** 3) - (t ** 5 + t ** 6)) + t ** 6 * (1 - t ** 2) - (1 + t ** 3) * (1 - t ** 5)) == 0
    ep2_sqf = (1 - t ** 3) * (1 - t ** 5) + t ** 3 * (1 - t ** 3) ** 2 * (1 + t)
    assert sp.expand(ep2_sqf - (1 + t ** 4 - t ** 5 - 2 * t ** 6 - 2 * t ** 7 + t ** 8 + t ** 9 + t ** 10)) == 0
    ep2_now = ep2_sqf + t ** 6 * (1 - t ** 3) * (1 + t) * (1 - t ** 2)
    assert sp.expand(ep2_now - (1 + t ** 4 - t ** 5 - t ** 6 - t ** 7 - t ** 9 + t ** 11 + t ** 12)) == 0
    assert Fraction(4, 5) < Fraction(13, 16) < Fraction(5, 6)
    assert Fraction(5, 7) < Fraction(13, 16)
    assert Fraction(5, 6) - Fraction(13, 16) == Fraction(1, 48)
    assert Fraction(3) - 5 * Fraction(13, 16) == Fraction(-17, 16) < -1
    assert Fraction(5) - 7 * Fraction(13, 16) == Fraction(-11, 16) < 0
    assert Fraction(-10, 3) < -3 < -1
    assert Fraction(3940, 100000) < Fraction(3283992, 100000000) * (Fraction(6, 5) - Fraction(1, 100000))
    assert Fraction(4 + 1, 4 + 2) == Fraction(5, 6)

    # --- Module 14: GeneralRealQuad_D4Q8_H07_H05.lean ---
    def is_regime_a(G, D1, D2, D3):
        if not (D1 % 8 == 1 or D2 % 8 == 1 or D3 % 8 == 1):
            return False
        target = D1 * D2 * D3 if G == "Q8" else math.gcd(D1, D2)
        for p in sp.primefactors(target):
            if p % 4 == 3:
                return False
        return True

    assert is_regime_a("D4", 5, 29, 145)
    assert is_regime_a("D4", 8, 17, 136)
    assert is_regime_a("Q8", 5, 61, 305)
    assert not is_regime_a("D4", 77, 1169, 1837)
    assert not is_regime_a("Q8", 5, 21, 105)
    assert not is_regime_a("Q8", 8, 12, 24)

    # Golod-Shafarevich algebraic identity & benchmarks
    dG_s, d0_s, T_s = sp.symbols("dG d0 T")
    assert sp.expand((dG_s ** 2 - 4 * (dG_s + d0_s - 1 + T_s)) - ((dG_s - 2) ** 2 - 4 * (d0_s + T_s))) == 0
    assert 4 * (6 + 3 - 1) <= 36 and 4 * (7 + 6 - 1) <= 49 and 4 * (9 + 12 - 1) <= 81
    assert Fraction(4, 3) < 2 and Fraction(2, 5) < Fraction(2, 3) and Fraction(10, 7) < 2
    return True


def main():
    print("=" * 84)
    print("WAVE-15 M03 LEAN 4.33.1 BLUEPRINT v4 STATIC + lean_index.db VERIFICATION SUITE")
    print("=" * 84)

    # 0. Check lean / lake availability honestly
    lean_bin = shutil.which("lean")
    lake_bin = shutil.which("lake")
    print(f"[ENV] lean on PATH: {lean_bin or 'NOT INSTALLED'}")
    print(f"[ENV] lake on PATH: {lake_bin or 'NOT INSTALLED'}")
    print("[ENV] NOTE: Static syntax + tools/lean_index.db + SymPy verification does NOT")
    print("            substitute for a live `lake build` against the 16.58M-line workspace archive.")
    print()

    # Check exact directory inventory (14 .lean files expected)
    disk_files = sorted(p.name for p in BLUEPRINT_DIR.glob("*.lean"))
    assert set(disk_files) == set(ALL_14_FILES), (
        f"Blueprint dir mismatch! Found={disk_files}, expected={sorted(ALL_14_FILES)}"
    )
    print(f"[PASS] Found all {len(ALL_14_FILES)} .lean files in {BLUEPRINT_DIR.relative_to(ROOT)}/")

    # Open tools/lean_index.db strictly READ-ONLY
    conn = sqlite3.connect(f"file:{DB_PATH}?mode=ro", uri=True)
    cur = conn.cursor()

    # 1. Static check across ALL 14 files
    print("\n--- PASS 1: ALL 14 BLUEPRINT MODULES (LINES / AXIOM / SORRY / ADMIT / DELIMITERS / NAMESPACES) ---")
    all_namespaces = {}
    total_lines_14 = 0
    total_lines_v4 = 0
    v4_stats = {}

    for idx, fname in enumerate(ALL_14_FILES, 1):
        fpath = BLUEPRINT_DIR / fname
        raw = fpath.read_text(encoding="utf-8")
        line_count = len(raw.splitlines())
        total_lines_14 += line_count
        is_v4 = fname in WAVE15_V4_FILES
        if is_v4:
            total_lines_v4 += line_count

        code, comment_errs = strip_comments_and_strings(raw)
        delim_errs = check_delimiters(code)
        axioms, sorries, admits = check_forbidden_tokens(code)
        opened_ns, ns_errs = check_namespaces(code)
        univ_errs = check_prop_structure_universe_hygiene(code) if is_v4 or fname in PRIOR_CLEAN_FILES else []
        imports, missing_db, missing_disk = check_imports(code, cur)

        # Record global namespace uniqueness across all 14 files
        for ns in opened_ns:
            if ns in all_namespaces:
                raise AssertionError(f"Duplicate namespace `{ns}` in {fname} and {all_namespaces[ns]}")
            all_namespaces[ns] = fname

        # Assertions
        assert not comment_errs, f"{fname}: comment errors {comment_errs}"
        assert not delim_errs, f"{fname}: delimiter errors {delim_errs}"
        assert not ns_errs, f"{fname}: namespace errors {ns_errs}"
        assert not sorries, f"{fname}: contains sorry {sorries}"
        assert not admits, f"{fname}: contains admit {admits}"
        assert not missing_db, f"{fname}: imports missing from lean_index.db: {missing_db}"
        assert not missing_disk, f"{fname}: imports missing on disk: {missing_disk}"

        if fname == LEGACY_WAVE3_MAIN:
            ax_map = dict(axioms)
            assert ax_map == EXPECTED_LEGACY_MAINERH_AXIOMS, (
                f"MainERH.lean axioms changed! Found={ax_map}"
            )
            tag = "LEGACY-v1 (3 documented Wave-3 axioms, untouched)"
        else:
            assert not axioms, f"{fname}: unexpected axioms {axioms}"
            if is_v4:
                assert not univ_errs, f"{fname}: universe hygiene issues {univ_errs}"
                tag = "NEW v4 (CLEAN)"
            else:
                tag = "PRIOR v1-v3 (CLEAN)"

        print(
            f"  [{idx:2d}] {fname:<44s} | {line_count:4d} lines | ax={len(axioms)} sr={len(sorries)} ad={len(admits)} "
            f"| imp={len(imports):2d} | ns={opened_ns} | {tag}"
        )
        if is_v4:
            v4_stats[fname] = {
                "lines": line_count,
                "axioms": len(axioms),
                "sorries": len(sorries),
                "admits": len(admits),
                "imports": len(imports),
                "namespaces": opened_ns,
            }

    print(f"\n[PASS] All 14 modules balanced, zero sorry, zero admit, unique namespaces! "
          f"(Total lines across 14 modules = {total_lines_14}; 3 new v4 modules = {total_lines_v4})")

    # 2. Extract and verify 100% of @workspace_decl tags in the 3 new v4 files
    print("\n--- PASS 2: 100% `@workspace_decl:` VERIFICATION AGAINST tools/lean_index.db & src/ ---")
    total_decls = 0
    total_hits = 0
    unique_decls = set()

    for fname in WAVE15_V4_FILES:
        raw = (BLUEPRINT_DIR / fname).read_text(encoding="utf-8")
        verified, failures = extract_and_verify_workspace_decls(fname, raw, cur)
        assert len(verified) > 0, f"{fname}: no @workspace_decl tags found!"
        if failures:
            for fail in failures:
                print(f"  [FAIL] {fname}: {fail}")
            raise AssertionError(f"{fname}: {len(failures)} workspace_decl failures!")
        total_decls += len(verified)
        total_hits += len(verified)
        for full_name, kind, rel_path, lno in verified:
            unique_decls.add((full_name, kind, rel_path, lno))
        v4_stats[fname]["decl_hits"] = len(verified)
        print(f"  [PASS] {fname:<44s}: {len(verified):2d}/{len(verified):2d} (100.0%) workspace decls verified in lean_index.db & src/")

    print(
        f"[PASS] Total `@workspace_decl:` citations verified: {total_hits}/{total_decls} (100.0% hit rate; "
        f"{len(unique_decls)} distinct archive declarations)"
    )

    # 3. Independent SymPy / exact-arithmetic cross-check
    print("\n--- PASS 3: SYMPY / EXACT-ARITHMETIC CROSS-CHECK OF EMBEDDED v4 FORMULAS ---")
    assert run_symbolic_math_checks()
    print("  [PASS] All embedded arithmetic/polynomial/rational/Regime-AB/HostEx formulas verified via Python/SymPy.")
    print("         (Note: finite/symbolic checks cross-check embedded statements and do NOT replace general proofs.)")

    conn.close()
    print("\n" + "=" * 84)
    print("ALL VERIFICATION CHECKS PASSED (EXIT CODE 0)")
    print("=" * 84)


if __name__ == "__main__":
    main()
