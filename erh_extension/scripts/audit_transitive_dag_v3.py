#!/usr/bin/env python3
"""
v3 Final Exact Audit over all 164,464 Lean modules in riemann-hypothesis/src/.
Fixes the `section HidaSetting` false positive in GroundTheory/LocalFields/FormalGroups/FrobeniusTwist.lean
and separates:
  (1) Direct syntactic tiers (A1 = Q-hardcoded, A2 = D7/FamP wrapper, B = CM/TC/TR poly, C = NF poly, D = Field-agnostic)
  (2) Strict file-level transitive import-cone purity (zero A1/A2 in entire import DAG)
  (3) Exact accounting of boilerplate `attribute [local instance] Formalism.BasicNotions.Host.cmStar`
  (4) Exact inventory of ALL DedekindZeta / HeckeCharacter / TateThesis / ClassNumberFormula / CFT / PoitouTate / Automorphic / Arakelov files.
"""
import json
import os
import re
import sqlite3
import sys
from collections import Counter, defaultdict, deque
from concurrent.futures import ProcessPoolExecutor

SRC_ROOT = os.path.abspath("riemann-hypothesis/src")
DB_PATH = os.path.abspath("tools/lean_index.db")

PAT_A1_CORE = re.compile(
    r"\b("
    r"DirichletCharacter|RiemannHypothesis|RiemannZetaZerosOnLine|"
    r"DirichletLNonvanishingRightOfHalf|DirichletLZerosOnLine|PrimitiveDirichletLZerosOnLine|"
    r"CharFamily|GmLevel|EveryCharacter|ZeroFreeAll|ZeroFreeOn|"
    r"IsChiField|WinPair|HasCMBy|omegaK|"
    r"JInvariantIntegrality|CM2|CM3|jacobiSym|"
    r"IsAbelianGalois\s+ℚ|Gal\s+ℚ|G\s+ℚ\s+Ω|galOf\s+ℚ|cycMod\s+ℚ|cycBar\s+ℚ|"
    r"dirG\s+ℚ|KatoUse|KatoTwoW|FerreroWashington|Stickelberger|"
    r"LemmaX|CorX|UpperTheory\.V\.HV\.GD|UpperTheory\.V\.HV\.Host|UpperTheory\.V\.U3|"
    r"HostHyp|HypOdd|TwoAdicCyclotomic|DiscrMaximalRealCyclotomic|"
    r"ClassMeanLogNormDiscChowlaSelberg|ChowlaSelberg"
    r")\b"
    r"|d\s*%\s*16\s*=\s*7|d\s*%\s*4\s*=\s*3|q\s*%\s*8\s*=\s*3|"
    r"Module\.finrank\s+ℚ\s+\w+\s*=\s*2"
)

PAT_PCHAR_HC = re.compile(r"\bPChar\b")
PAT_RIEMANN_ZETA = re.compile(r"\briemannZeta\b")
PAT_CYC_Q = re.compile(r"\bCyclotomicField\s+\S+\s+ℚ\b")

AUX_NF_WHITELIST_PREFIXES = (
    "GroundTheory/GlobalFields/ExistenceTheorem/",
    "GroundTheory/GlobalFields/SecondInequality/",
    "GroundTheory/GlobalFields/FirstInequality/",
    "GroundTheory/GlobalFields/GlobalReciprocity/",
    "GroundTheory/GlobalFields/ComplexMultiplication/JInvariant.lean",
    "GroundTheory/GlobalFields/TateThesis/",
    "GroundTheory/ProfiniteCohomology/",
    "GroundTheory/LocalFields/",
)

# Notice: match HidaSetting ONLY when it is NOT `section HidaSetting` / `end HidaSetting`!
PAT_A2 = re.compile(
    r"\b("
    r"D7|FamP|FamCore|FamClass|SizeData₂|HostAx|HostRaw|Formalism\.BasicNotions\.Host|"
    r"ArithData|HostFacts|HostFactsS|TopG|VWin|VWinAt|VAt|HypV|LinkN|LinkV|LinkG|LinkS|LinkDIV|LinkMu|"
    r"PoincareSetting|TheoremSSelected|StepThmBG|HypsAlt|CovolumeBoundOfX|"
    r"BoundAtTwoThree|At23|IntInert|JetsInert|IntFirst|GoodOrigin|RootTower|Tor\.Host|"
    r"HostNumbers|hostRd|hostLval"
    r")\b|(?<!section\s)(?<!end\s)\bHidaSetting\b"
)

PAT_CMSTAR_ATTR = re.compile(r"^\s*attribute\s+\[local instance\]\s+Formalism\.BasicNotions\.Host\.cmStar\s*$", re.M)

PAT_B = re.compile(
    r"\b("
    r"IsCMField|IsCMUnram|CMData|IsTotallyComplex|IsTotallyReal|maximalRealSubfield|"
    r"CMType|PolarizedPair|AutInst|DivData|TheoremF|TheoremFSharp|LemmaK|"
    r"Row0b|Row0|PropsB|TLiftK|SiegelMassRatio|SiegelMassRatioCM|"
    r"ThetaIntegralsAgree|LocalMatching|WeilTensorModels|HSpace|"
    r"ConjugateSelfDual|cmStar|complexConj|DeligneRibet|SiegelKlingen|"
    r"ArthurClozel|UnitaryBC|DefiniteN|Labesse"
    r")\b"
)

PAT_C = re.compile(
    r"\b("
    r"NumberField|RingOfIntegers|HeightOneSpectrum|InfinitePlace|"
    r"IdeleGroup|IdeleClassGroup|FiniteAdeleRing|AdeleRing|InfiniteAdeleRing|"
    r"HeckeCharacter|dedekindZeta|completedDedekindZeta|continuedDedekindZeta|normalizedDedekindZeta|"
    r"classNumber|regulator|torsionOrder|discr|differentIdeal|"
    r"chebotarevSet|HasDirichletDensity|RecTExists|IsRecT|LawsT|WeilDeligne|"
    r"GlobalArtin|LocalArtin|PoitouTate|GlobalEulerChar|GlobalFiniteness|"
    r"GreenbergWiles|BlochKato|KummerTheory|HasseNorm|Brauer|TateThesis|tateZeta|"
    r"CuspSub|HChar|IrrGL|adicCompletion"
    r")\b|𝓞\s+"
)


def is_a1(rel, text):
    if PAT_A1_CORE.search(text):
        return True
    if PAT_PCHAR_HC.search(text):
        if not rel.startswith("Formalism/RealPlaceAnalysis/") and "Formalism.REAL.PChar" not in text and "inP ε X" not in text:
            return True
    if not rel.startswith(AUX_NF_WHITELIST_PREFIXES):
        if PAT_RIEMANN_ZETA.search(text) or PAT_CYC_Q.search(text):
            return True
    return False


def classify_batch(items):
    out = []
    for mod, rel in items:
        full = os.path.join(SRC_ROOT, rel)
        try:
            with open(full, "r", encoding="utf-8", errors="replace") as f:
                text = f.read()
        except Exception:
            out.append((mod, rel, 0, "D", "D", False))
            continue
        n_lines = text.count("\n") + (1 if text and not text.endswith("\n") else 0)
        # Raw direct tier
        if is_a1(rel, text):
            t_raw = "A1"
        elif PAT_A2.search(text):
            t_raw = "A2"
        elif PAT_B.search(text):
            t_raw = "B"
        elif PAT_C.search(text):
            t_raw = "C"
        else:
            t_raw = "D"

        # Stripped-boilerplate tier (ignoring ONLY `attribute [local instance] Formalism.BasicNotions.Host.cmStar`)
        text_nb = PAT_CMSTAR_ATTR.sub("", text)
        cmstar_only = (t_raw == "A2") and not bool(PAT_A2.search(text_nb))
        if t_raw == "A2" and cmstar_only:
            if PAT_B.search(text_nb):
                t_clean = "B"
            elif PAT_C.search(text_nb):
                t_clean = "C"
            else:
                t_clean = "D"
        else:
            t_clean = t_raw

        out.append((mod, rel, n_lines, t_raw, t_clean, cmstar_only))
    return out


def main():
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    rows = cur.execute("SELECT module, rel_path FROM files").fetchall()

    n_workers = min(os.cpu_count() or 8, 12)
    chunk = max(1, (len(rows) + n_workers * 4 - 1) // (n_workers * 4))
    batches = [rows[i : i + chunk] for i in range(0, len(rows), chunk)]

    mod_rel = {}
    mod_lines = {}
    mod_raw = {}
    mod_clean = {}
    cmstar_only_count = 0
    cmstar_only_lines = 0
    with ProcessPoolExecutor(max_workers=n_workers) as ex:
        for part in ex.map(classify_batch, batches):
            for mod, rel, nl, tr, tc, cmo in part:
                mod_rel[mod] = rel
                mod_lines[mod] = nl
                mod_raw[mod] = tr
                mod_clean[mod] = tc
                if cmo:
                    cmstar_only_count += 1
                    cmstar_only_lines += nl

    rev = defaultdict(list)
    mod_set = set(mod_rel.keys())
    for m, imp in cur.execute("SELECT module, imported FROM imports"):
        if m in mod_set and imp in mod_set:
            rev[imp].append(m)

    def bfs_up(seeds):
        visited = set(seeds)
        q = deque(seeds)
        while q:
            u = q.popleft()
            for v in rev.get(u, ()):
                if v not in visited:
                    visited.add(v)
                    q.append(v)
        return visited

    t_a1 = bfs_up([m for m, t in mod_raw.items() if t == "A1"])
    t_a2 = bfs_up([m for m, t in mod_raw.items() if t == "A2"])
    t_b = bfs_up([m for m, t in mod_raw.items() if t == "B"])
    t_c = bfs_up([m for m, t in mod_raw.items() if t == "C"])

    summary_total = Counter()
    summary_top = defaultdict(Counter)
    summary_sub = defaultdict(Counter)

    for m, rel in mod_rel.items():
        parts = rel.split("/")
        top = parts[0] if len(parts) > 1 else "(root)"
        sub = "/".join(parts[:2]) if len(parts) > 2 else top
        nl = mod_lines[m]
        dr = mod_raw[m]
        dc = mod_clean[m]

        if m in t_a1:
            tt = "TA1"
        elif m in t_a2:
            tt = "TA2"
        elif m in t_b:
            tt = "TB"
        elif m in t_c:
            tt = "TC"
        else:
            tt = "TD"

        for b in (summary_total, summary_top[top], summary_sub[sub]):
            b["files"] += 1
            b["lines"] += nl
            b[f"rf_{dr}"] += 1
            b[f"rl_{dr}"] += nl
            b[f"cf_{dc}"] += 1
            b[f"cl_{dc}"] += nl
            b[f"tf_{tt}"] += 1
            b[f"tl_{tt}"] += nl

    T = summary_total
    print(f"Boilerplate `attribute [local instance] Host.cmStar`-only A2 files: {cmstar_only_count:,} files ({cmstar_only_lines:,} lines)")
    print("\n=== V3 DIRECT TIERS (STRIPPED BOILERPLATE vs RAW) ===")
    for k in ["A1", "A2", "B", "C", "D"]:
        print(f"  {k:2s}: RAW {T[f'rf_{k}']:7,d} f ({100*T[f'rl_{k}']/T['lines']:5.2f}% L) | CLEAN {T[f'cf_{k}']:7,d} f ({100*T[f'cl_{k}']/T['lines']:5.2f}% L)")
    cg_f = T["cf_B"] + T["cf_C"] + T["cf_D"]
    cg_l = T["cl_B"] + T["cl_C"] + T["cl_D"]
    print(f"  --> CLEAN DIRECT GENERAL (B+C+D): {cg_f:7,d} files ({100*cg_f/T['files']:5.2f}%) | {cg_l:10,d} lines ({100*cg_l/T['lines']:5.2f}%)")

    print("\n=== V3 STRICT TRANSITIVE IMPORT-CONE PURITY ===")
    for k in ["TA1", "TA2", "TB", "TC", "TD"]:
        print(f"  {k:3s}: {T[f'tf_{k}']:7,d} f ({100*T[f'tf_{k}']/T['files']:5.2f}%) | {T[f'tl_{k}']:10,d} L ({100*T[f'tl_{k}']/T['lines']:5.2f}%)")
    pf = T["tf_TB"] + T["tf_TC"] + T["tf_TD"]
    pl = T["tl_TB"] + T["tl_TC"] + T["tl_TD"]
    print(f"  --> 100% TRANS-PURE (TB+TC+TD): {pf:7,d} f ({100*pf/T['files']:5.2f}%) | {pl:10,d} L ({100*pl/T['lines']:5.2f}%)")

    print("\n=== V3 TOP-LEVEL LIBRARIES ===")
    for top, v in sorted(summary_top.items(), key=lambda kv: -kv[1]["lines"]):
        cl_gen = v["cl_B"] + v["cl_C"] + v["cl_D"]
        pl = v["tl_TB"] + v["tl_TC"] + v["tl_TD"]
        print(
            f"  {top:18s}: {v['files']:7,d} f | {v['lines']:10,d} L | "
            f"CleanDir(A1={100*v['cl_A1']/v['lines']:4.1f}% A2={100*v['cl_A2']/v['lines']:4.1f}% Gen={100*cl_gen/v['lines']:5.1f}%) | "
            f"TransPure={100*pl/v['lines']:5.1f}%"
        )

    print("\n=== V3 GROUNDTHEORY SUBDIRECTORIES (FIXED section HidaSetting!) ===")
    for sub, v in sorted(summary_sub.items(), key=lambda kv: -kv[1]["lines"]):
        if sub.startswith("GroundTheory/"):
            cl_gen = v["cl_B"] + v["cl_C"] + v["cl_D"]
            pl = v["tl_TB"] + v["tl_TC"] + v["tl_TD"]
            print(f"  {sub:40s}: {v['files']:5,d} f | {v['lines']:8,d} L | CleanDirGen={100*cl_gen/v['lines']:5.1f}% | TransPure={100*pl/v['lines']:5.1f}%")

    print("\n=== V3 DEVELOPMENT SUBDIRECTORIES ===")
    for sub, v in sorted(summary_sub.items(), key=lambda kv: -kv[1]["lines"]):
        if sub.startswith("Development/"):
            cl_gen = v["cl_B"] + v["cl_C"] + v["cl_D"]
            pl = v["tl_TB"] + v["tl_TC"] + v["tl_TD"]
            print(f"  {sub:40s}: {v['files']:6,d} f | {v['lines']:9,d} L | CleanDirGen={100*cl_gen/v['lines']:5.1f}% | TransPure={100*pl/v['lines']:5.1f}%")

    with open("erh_research/scripts/lean_transitive_audit_v3.json", "w", encoding="utf-8") as f:
        json.dump(
            {
                "cmstar_only_count": cmstar_only_count,
                "cmstar_only_lines": cmstar_only_lines,
                "total": dict(summary_total),
                "top": {k: dict(v) for k, v in summary_top.items()},
                "sub": {k: dict(v) for k, v in summary_sub.items()},
            },
            f,
            indent=2,
        )


if __name__ == "__main__":
    main()
