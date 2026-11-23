#!/usr/bin/env python3
"""
Refined v2 Transitive Import-DAG Generalization Audit over all 164,464 Lean modules.
Fixes false positives discovered in v1 diagnostics:
  1. Excludes Formalism.REAL.PChar (Lie-algebra Cartan p-characterization for U(p,q) over R),
     matching only Formalism.HC.PChar (primitive Dirichlet character).
  2. Excludes auxiliary uses of riemannZeta (Eisenstein series constant term) and CyclotomicField
     (Kummer root-of-unity adjunction) inside general-number-field theorems of GroundTheory/GlobalFields
     (ExistenceTheorem, SecondInequality, GlobalReciprocity, TateThesis, ComplexMultiplication/JInvariant).
  3. Reports BOTH Direct Syntactic Tiers AND Transitive Import-Cone Purity, PLUS exact fan-out analysis.
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

# A1: Intrinsically tied to Q / Dirichlet characters / riemannZeta / Cyclotomic over Q / Q(sqrt(-d)) / G_Q
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

# Files where CyclotomicField/riemannZeta appear purely as auxiliary internal proof gadgets
# inside theorems polymorphic over arbitrary [Field K] [NumberField K]
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

# A2: Coupled through the D7 / FamP / Host / ArithData / HostAx / Tor.Host wrapper containers
PAT_A2 = re.compile(
    r"\b("
    r"D7|FamP|FamCore|FamClass|SizeData₂|HostAx|HostRaw|Formalism\.BasicNotions\.Host|"
    r"ArithData|HostFacts|HostFactsS|TopG|VWin|VWinAt|VAt|HypV|LinkN|LinkV|LinkG|LinkS|LinkDIV|LinkMu|"
    r"HidaSetting|PoincareSetting|TheoremSSelected|StepThmBG|HypsAlt|CovolumeBoundOfX|"
    r"BoundAtTwoThree|At23|IntInert|JetsInert|IntFirst|GoodOrigin|RootTower|Tor\.Host|"
    r"HostNumbers|hostRd|hostLval"
    r")\b"
)

# B: Explicitly polymorphic over CM / Totally Real / Totally Complex number fields
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

# C: Explicitly polymorphic over arbitrary NumberFields / Global fields / Idele / Hecke / DedekindZeta
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
    # PChar is ONLY A1 outside Formalism/RealPlaceAnalysis (where PChar = Lie algebra Cartan p-char)
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
            out.append((mod, rel, 0, "D"))
            continue
        n_lines = text.count("\n") + (1 if text and not text.endswith("\n") else 0)
        if is_a1(rel, text):
            t = "A1"
        elif PAT_A2.search(text):
            t = "A2"
        elif PAT_B.search(text):
            t = "B"
        elif PAT_C.search(text):
            t = "C"
        else:
            t = "D"
        out.append((mod, rel, n_lines, t))
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
    mod_direct = {}
    with ProcessPoolExecutor(max_workers=n_workers) as ex:
        for part in ex.map(classify_batch, batches):
            for mod, rel, nl, t in part:
                mod_rel[mod] = rel
                mod_lines[mod] = nl
                mod_direct[mod] = t

    rev = defaultdict(list)
    fwd = defaultdict(list)
    mod_set = set(mod_rel.keys())
    for m, imp in cur.execute("SELECT module, imported FROM imports"):
        if m in mod_set and imp in mod_set:
            rev[imp].append(m)
            fwd[m].append(imp)

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

    seeds_a1 = [m for m, t in mod_direct.items() if t == "A1"]
    seeds_a2 = [m for m, t in mod_direct.items() if t == "A2"]
    seeds_b = [m for m, t in mod_direct.items() if t == "B"]
    seeds_c = [m for m, t in mod_direct.items() if t == "C"]

    t_a1 = bfs_up(seeds_a1)
    t_a2 = bfs_up(seeds_a2)
    t_b = bfs_up(seeds_b)
    t_c = bfs_up(seeds_c)

    summary_total = Counter()
    summary_top = defaultdict(Counter)
    summary_sub = defaultdict(Counter)
    summary_sub3 = defaultdict(Counter)

    for m, rel in mod_rel.items():
        parts = rel.split("/")
        top = parts[0] if len(parts) > 1 else "(root)"
        sub = "/".join(parts[:2]) if len(parts) > 2 else top
        sub3 = "/".join(parts[:3]) if len(parts) > 3 else sub
        nl = mod_lines[m]
        dt = mod_direct[m]

        if m in t_a1:
            tt = "TA1_Q_CONE"
        elif m in t_a2:
            tt = "TA2_WRAPPER_CONE"
        elif m in t_b:
            tt = "TB_CM_TC_TR_PURE"
        elif m in t_c:
            tt = "TC_NF_PURE"
        else:
            tt = "TD_AGNOSTIC_PURE"

        for b in (summary_total, summary_top[top], summary_sub[sub], summary_sub3[sub3]):
            b["files"] += 1
            b["lines"] += nl
            b[f"df_{dt}"] += 1
            b[f"dl_{dt}"] += nl
            b[f"tf_{tt}"] += 1
            b[f"tl_{tt}"] += nl

    # Top A1 fanout
    a1_fanout = []
    for m in seeds_a1:
        reach = bfs_up([m])
        a1_fanout.append((len(reach), m, mod_rel[m]))
    a1_fanout.sort(reverse=True)

    # Also check: what are the exact GroundTheory subdirectories?
    T = summary_total
    print("=== V2 DIRECT SYNTACTIC TIERS (ALL 164,464 MODULES) ===")
    for k in ["A1", "A2", "B", "C", "D"]:
        fc, lc = T[f"df_{k}"], T[f"dl_{k}"]
        print(f"  Direct {k:2s}: {fc:7,d} files ({100*fc/T['files']:5.2f}%) | {lc:10,d} lines ({100*lc/T['lines']:5.2f}%)")
    dg_f = T["df_B"] + T["df_C"] + T["df_D"]
    dg_l = T["dl_B"] + T["dl_C"] + T["dl_D"]
    print(f"  --> DIRECT GENERAL (B+C+D): {dg_f:7,d} files ({100*dg_f/T['files']:5.2f}%) | {dg_l:10,d} lines ({100*dg_l/T['lines']:5.2f}%)")

    print("\n=== V2 TRANSITIVE IMPORT-CONE PURITY (ALL 164,464 MODULES) ===")
    for k in ["TA1_Q_CONE", "TA2_WRAPPER_CONE", "TB_CM_TC_TR_PURE", "TC_NF_PURE", "TD_AGNOSTIC_PURE"]:
        fc, lc = T[f"tf_{k}"], T[f"tl_{k}"]
        print(f"  {k:20s}: {fc:7,d} files ({100*fc/T['files']:5.2f}%) | {lc:10,d} lines ({100*lc/T['lines']:5.2f}%)")
    pf = T["tf_TB_CM_TC_TR_PURE"] + T["tf_TC_NF_PURE"] + T["tf_TD_AGNOSTIC_PURE"]
    pl = T["tl_TB_CM_TC_TR_PURE"] + T["tl_TC_NF_PURE"] + T["tl_TD_AGNOSTIC_PURE"]
    print(f"  --> 100% TRANSITIVELY PURE GENERAL (TB+TC+TD): {pf:7,d} files ({100*pf/T['files']:5.2f}%) | {pl:10,d} lines ({100*pl/T['lines']:5.2f}%)")

    print("\n=== V2 BY TOP-LEVEL LIBRARY ===")
    for top, v in sorted(summary_top.items(), key=lambda kv: -kv[1]["lines"]):
        dl_gen = v["dl_B"] + v["dl_C"] + v["dl_D"]
        pl = v["tl_TB_CM_TC_TR_PURE"] + v["tl_TC_NF_PURE"] + v["tl_TD_AGNOSTIC_PURE"]
        print(
            f"  {top:18s}: {v['files']:7,d} f | {v['lines']:10,d} L | "
            f"Dir(A1={100*v['dl_A1']/v['lines']:4.1f}% A2={100*v['dl_A2']/v['lines']:4.1f}% Gen={100*dl_gen/v['lines']:5.1f}%) | "
            f"TransPure={100*pl/v['lines']:5.1f}% (TB={100*v['tl_TB_CM_TC_TR_PURE']/v['lines']:4.1f}% TC={100*v['tl_TC_NF_PURE']/v['lines']:4.1f}% TD={100*v['tl_TD_AGNOSTIC_PURE']/v['lines']:4.1f}%)"
        )

    print("\n=== V2 GROUNDTHEORY SUBDIRECTORIES ===")
    for sub, v in sorted(summary_sub.items(), key=lambda kv: -kv[1]["lines"]):
        if sub.startswith("GroundTheory/"):
            dl_gen = v["dl_B"] + v["dl_C"] + v["dl_D"]
            pl = v["tl_TB_CM_TC_TR_PURE"] + v["tl_TC_NF_PURE"] + v["tl_TD_AGNOSTIC_PURE"]
            print(f"  {sub:40s}: {v['files']:5,d} f | {v['lines']:8,d} L | DirGen={100*dl_gen/v['lines']:5.1f}% | TransPure={100*pl/v['lines']:5.1f}%")

    print("\n=== V2 DEVELOPMENT SUBDIRECTORIES ===")
    for sub, v in sorted(summary_sub.items(), key=lambda kv: -kv[1]["lines"]):
        if sub.startswith("Development/"):
            dl_gen = v["dl_B"] + v["dl_C"] + v["dl_D"]
            pl = v["tl_TB_CM_TC_TR_PURE"] + v["tl_TC_NF_PURE"] + v["tl_TD_AGNOSTIC_PURE"]
            print(f"  {sub:40s}: {v['files']:6,d} f | {v['lines']:9,d} L | DirGen={100*dl_gen/v['lines']:5.1f}% | TransPure={100*pl/v['lines']:5.1f}%")

    print("\n=== V2 COMPANION / RECIPROCITY / POSITIVITY TOP SUBDIRS ===")
    for sub, v in sorted(summary_sub.items(), key=lambda kv: -kv[1]["lines"]):
        if sub.startswith(("CompanionTheory/", "ReciprocityTheory/", "PositivityTheory/")):
            if v["lines"] >= 5000:
                dl_gen = v["dl_B"] + v["dl_C"] + v["dl_D"]
                pl = v["tl_TB_CM_TC_TR_PURE"] + v["tl_TC_NF_PURE"] + v["tl_TD_AGNOSTIC_PURE"]
                print(f"  {sub:44s}: {v['files']:5,d} f | {v['lines']:8,d} L | DirGen={100*dl_gen/v['lines']:5.1f}% | TransPure={100*pl/v['lines']:5.1f}%")

    print("\n=== V2 TOP 15 HIGHEST FAN-OUT A1 MODULES ===")
    for cnt, m, rel in a1_fanout[:15]:
        print(f"  reach={cnt:7,d} | {rel}")

    with open("erh_research/scripts/lean_transitive_audit_v2.json", "w", encoding="utf-8") as f:
        json.dump(
            {
                "total": dict(summary_total),
                "top": {k: dict(v) for k, v in summary_top.items()},
                "sub": {k: dict(v) for k, v in summary_sub.items()},
                "sub3": {k: dict(v) for k, v in summary_sub3.items()},
                "top_a1_fanout": a1_fanout[:30],
            },
            f,
            indent=2,
        )


if __name__ == "__main__":
    main()
