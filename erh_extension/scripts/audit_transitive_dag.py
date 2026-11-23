#!/usr/bin/env python3
"""
Transitive Import-DAG Generalization Audit over all 164,464 Lean modules in riemann-hypothesis/src/.
Combines direct syntactic classification with exact transitive import-closure propagation via tools/lean_index.db.
Also produces full second-level & third-level breakdowns and spot-check validation samples.
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

# Tightened, high-precision patterns:
# A1: Intrinsically tied to Q / Dirichlet characters / riemannZeta / CyclotomicField / Q(sqrt(-d)) / G_Q
PAT_A1 = re.compile(
    r"\b("
    r"DirichletCharacter|riemannZeta|RiemannHypothesis|RiemannZetaZerosOnLine|"
    r"DirichletLNonvanishingRightOfHalf|DirichletLZerosOnLine|PrimitiveDirichletLZerosOnLine|"
    r"PChar|CharFamily|GmLevel|EveryCharacter|ZeroFreeAll|ZeroFreeOn|"
    r"CyclotomicField|IsChiField|WinPair|HasCMBy|omegaK|"
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
        if PAT_A1.search(text):
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
    print(f"Loaded {len(rows):,} modules from lean_index.db", file=sys.stderr)

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

    print("Building project-local import graph...", file=sys.stderr)
    # reverse graph: imported -> list of importers
    rev = defaultdict(list)
    fwd = defaultdict(list)
    mod_set = set(mod_rel.keys())
    for m, imp in cur.execute("SELECT module, imported FROM imports"):
        if m in mod_set and imp in mod_set:
            rev[imp].append(m)
            fwd[m].append(imp)

    # Compute transitive flags:
    # trans_A1[m] = True iff m or some transitive import of m has direct == 'A1'
    # trans_A2[m] = True iff m or some transitive import of m has direct == 'A2'
    # trans_B[m]  = True iff m or some transitive import of m has direct == 'B'
    # trans_C[m]  = True iff m or some transitive import of m has direct == 'C'
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

    # Also compute transitive closure DOWN from Main to check live import cone!
    main_cone = set()
    if "Main" in mod_set:
        q = deque(["Main"])
        main_cone.add("Main")
        while q:
            u = q.popleft()
            for v in fwd.get(u, ()):
                if v not in main_cone:
                    main_cone.add(v)
                    q.append(v)

    print(f"Modules in Main transitive import cone: {len(main_cone):,} / {len(mod_set):,}", file=sys.stderr)

    # Assign transitive tier (strict precedence: TA1 > TA2 > TB > TC > TD)
    # Wait: also track a CLEAN separation:
    # - PURE_GENERAL (neither A1 nor A2 anywhere in transitive import cone) -> split into TB, TC, TD
    # - WRAPPER_ONLY (A2 in cone, NO A1 in cone)
    # - Q_CONTAMINATED (A1 in cone)
    # WAIT: let's check if A2 itself imports A1! Because D7/Host imports HostAx/HostHyp which is A1!
    # That's super illuminating — let's measure BOTH:
    # (1) Direct tier (A1, A2, B, C, D)
    # (2) Transitive tier (TA1, TA2_only, TB, TC, TD)
    summary_total = Counter()
    summary_top = defaultdict(Counter)
    summary_sub = defaultdict(Counter)

    for m, rel in mod_rel.items():
        parts = rel.split("/")
        top = parts[0] if len(parts) > 1 else "(root)"
        sub = "/".join(parts[:2]) if len(parts) > 2 else top
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

        for b in (summary_total, summary_top[top], summary_sub[sub]):
            b["files"] += 1
            b["lines"] += nl
            b[f"df_{dt}"] += 1
            b[f"dl_{dt}"] += nl
            b[f"tf_{tt}"] += 1
            b[f"tl_{tt}"] += nl
            if m in main_cone:
                b["in_main_files"] += 1
                b["in_main_lines"] += nl

    # Also check what causes A1 contamination in each top-level library (which A1 modules have highest reverse-import fan-out!)
    a1_fanout = []
    for m in seeds_a1:
        reach = bfs_up([m])
        a1_fanout.append((len(reach), m, mod_rel[m]))
    a1_fanout.sort(reverse=True)

    print("\n=== TRANSITIVE IMPORT-CONE AUDIT (ALL 164,464 MODULES) ===")
    T = summary_total
    for k in ["TA1_Q_CONE", "TA2_WRAPPER_CONE", "TB_CM_TC_TR_PURE", "TC_NF_PURE", "TD_AGNOSTIC_PURE"]:
        fc = T[f"tf_{k}"]
        lc = T[f"tl_{k}"]
        print(f"  {k:20s}: {fc:7,d} files ({100*fc/T['files']:5.2f}%) | {lc:10,d} lines ({100*lc/T['lines']:5.2f}%)")
    pure_f = T["tf_TB_CM_TC_TR_PURE"] + T["tf_TC_NF_PURE"] + T["tf_TD_AGNOSTIC_PURE"]
    pure_l = T["tl_TB_CM_TC_TR_PURE"] + T["tl_TC_NF_PURE"] + T["tl_TD_AGNOSTIC_PURE"]
    print(f"  --> 100% TRANSITIVELY PURE GENERAL (TB+TC+TD): {pure_f:7,d} files ({100*pure_f/T['files']:5.2f}%) | {pure_l:10,d} lines ({100*pure_l/T['lines']:5.2f}%)")

    print("\n=== TRANSITIVE PURITY BY TOP-LEVEL LIBRARY ===")
    for top, v in sorted(summary_top.items(), key=lambda kv: -kv[1]["lines"]):
        pf = v["tf_TB_CM_TC_TR_PURE"] + v["tf_TC_NF_PURE"] + v["tf_TD_AGNOSTIC_PURE"]
        pl = v["tl_TB_CM_TC_TR_PURE"] + v["tl_TC_NF_PURE"] + v["tl_TD_AGNOSTIC_PURE"]
        df_gen = v["df_B"] + v["df_C"] + v["df_D"]
        dl_gen = v["dl_B"] + v["dl_C"] + v["dl_D"]
        print(
            f"  {top:18s}: {v['files']:7,d} files | {v['lines']:10,d} lines | "
            f"DirectGen={100*dl_gen/v['lines']:5.1f}% | TransPure={100*pl/v['lines']:5.1f}% "
            f"(TB={100*v['tl_TB_CM_TC_TR_PURE']/v['lines']:4.1f}% TC={100*v['tl_TC_NF_PURE']/v['lines']:4.1f}% TD={100*v['tl_TD_AGNOSTIC_PURE']/v['lines']:4.1f}%)"
        )

    print("\n=== TOP 25 SECOND-LEVEL SUBDIRECTORIES BY LINE COUNT ===")
    for sub, v in sorted(summary_sub.items(), key=lambda kv: -kv[1]["lines"])[:35]:
        pl = v["tl_TB_CM_TC_TR_PURE"] + v["tl_TC_NF_PURE"] + v["tl_TD_AGNOSTIC_PURE"]
        dl_gen = v["dl_B"] + v["dl_C"] + v["dl_D"]
        print(
            f"  {sub:44s}: {v['files']:6,d} f | {v['lines']:9,d} L | "
            f"DirGen={100*dl_gen/v['lines']:5.1f}% | TransPure={100*pl/v['lines']:5.1f}%"
        )

    print("\n=== TOP 20 HIGHEST FAN-OUT A1 MODULES (Contamination Root Causes!) ===")
    for cnt, m, rel in a1_fanout[:20]:
        print(f"  reach={cnt:7,d} | {rel}")

    out_data = {
        "total": dict(summary_total),
        "top": {k: dict(v) for k, v in summary_top.items()},
        "sub": {k: dict(v) for k, v in summary_sub.items()},
        "top_a1_fanout": a1_fanout[:40],
        "main_cone_count": len(main_cone),
    }
    with open("erh_research/scripts/lean_transitive_audit.json", "w", encoding="utf-8") as f:
        json.dump(out_data, f, indent=2)


if __name__ == "__main__":
    main()
