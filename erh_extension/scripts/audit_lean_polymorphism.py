#!/usr/bin/env python3
"""
Exact archive-wide Lean 4.33.1 polymorphism & base-field audit for Track 17.
Scans all .lean files under riemann-hypothesis/src/ using multiprocessing,
computes exact file/line/non-blank/byte/declaration counts per top-level
and second-level directory, and classifies every file by base-field polymorphism.
"""
import json
import os
import re
import sys
from collections import Counter, defaultdict
from concurrent.futures import ProcessPoolExecutor

SRC_ROOT = os.path.abspath("riemann-hypothesis/src")

# Regex patterns (compiled per worker)
RE_DECL = re.compile(
    r"^\s*(?:private\s+|protected\s+|noncomputable\s+|local\s+|scoped\s+|@\[[^\]]*\]\s*)*"
    r"(theorem|lemma|def|structure|class|inductive|abbrev|instance|axiom)\b"
)
RE_SORRY = re.compile(r"\b(sorry|admit)\b")

# Tier A1: Explicitly hardcoded to Q / Dirichlet / Cyclotomic / Q(sqrt(-d)) / G_Q
PAT_A1 = re.compile(
    r"\b("
    r"DirichletCharacter|riemannZeta|RiemannHypothesis|RiemannZetaZerosOnLine|"
    r"DirichletLNonvanishingRightOfHalf|DirichletLZerosOnLine|PrimitiveDirichletLZerosOnLine|"
    r"PChar|CharFamily|GmLevel|EveryCharacter|ZeroFreeAll|ZeroFreeOn|"
    r"CyclotomicField|IsChiField|WinPair|HasCMBy|omegaK|"
    r"JInvariantIntegrality|CM2|CM3|jacobiSym|"
    r"IsAbelianGalois\s+ℚ|IsGalois\s+ℚ|Gal\s+ℚ|G\s+ℚ\s+Ω|galOf\s+ℚ|cycMod\s+ℚ|cycBar\s+ℚ|"
    r"dirG\s+ℚ|KatoUse|KatoTwoW|FerreroWashington|Stickelberger|"
    r"LemmaX|CorX|UpperTheory\.V\.HV\.GD|UpperTheory\.V\.HV\.Host|UpperTheory\.V\.U3|"
    r"HostHyp|HypOdd|TwoAdicCyclotomic|DiscrMaximalRealCyclotomic|"
    r"ClassMeanLogNormDiscChowlaSelberg|ChowlaSelberg"
    r")\b"
    r"|d\s*%\s*16\s*=\s*7|d\s*%\s*4\s*=\s*3|q\s*%\s*8\s*=\s*3|"
    r"Module\.finrank\s+ℚ\s+\w+\s*=\s*2"
)

# Tier A2: Coupled through the D7 / FamP / Host / ArithData / HostAx wrapper containers
PAT_A2 = re.compile(
    r"\b("
    r"D7|FamP|FamCore|FamClass|SizeData₂|HostAx|HostRaw|Formalism\.BasicNotions\.Host|"
    r"ArithData|HostFacts|HostFactsS|TopG|VWin|VWinAt|VAt|HypV|LinkN|LinkV|LinkG|LinkS|LinkDIV|LinkMu|"
    r"HidaSetting|PoincareSetting|TheoremSSelected|StepThmBG|HypsAlt|CovolumeBoundOfX|"
    r"BoundAtTwoThree|At23|IntInert|JetsInert|IntFirst|GoodOrigin|RootTower|Tor\.Host|"
    r"HostNumbers|hostRd|hostLval"
    r")\b"
)

# Tier B: Explicitly polymorphic over CM / Totally Real / Totally Complex number fields
PAT_B = re.compile(
    r"\b("
    r"IsCMField|IsCMUnram|CMData|IsTotallyComplex|IsTotallyReal|maximalRealSubfield|"
    r"CMType|PolarizedPair|AutInst|DivData|TheoremF|TheoremFSharp|LemmaK|"
    r"Row0b|Row0|PropsB|TLiftK|SiegelMassRatio|SiegelMassRatioCM|"
    r"ThetaIntegralsAgree|LocalMatching|WeilTensorModels|HSpace|"
    r"ConjugateSelfDual|StarRing|cmStar|complexConj|DeligneRibet|SiegelKlingen|"
    r"ArthurClozel|UnitaryBC|DefiniteN|Labesse"
    r")\b"
)

# Tier C: Explicitly polymorphic over arbitrary NumberFields / Global fields / Idele / Hecke / DedekindZeta
PAT_C = re.compile(
    r"\b("
    r"NumberField|RingOfIntegers|HeightOneSpectrum|InfinitePlace|"
    r"IdeleGroup|IdeleClassGroup|FiniteAdeleRing|AdeleRing|InfiniteAdeleRing|"
    r"HeckeCharacter|dedekindZeta|completedDedekindZeta|continuedDedekindZeta|normalizedDedekindZeta|"
    r"classNumber|regulator|torsionOrder|discr|differentIdeal|"
    r"chebotarevSet|HasDirichletDensity|RecTExists|IsRecT|LawsT|WD|WeilDeligne|"
    r"GlobalArtin|LocalArtin|PoitouTate|GlobalEulerChar|GlobalFiniteness|"
    r"GreenbergWiles|BlochKato|KummerTheory|HasseNorm|Brauer|TateThesis|tateZeta|"
    r"CuspSub|HChar|IrrGL|adicCompletion"
    r")\b|𝓞\s+"
)

# Extra targeted keyword counters for section 4 (ERH / general NF infrastructure)
SPECIFIC_TAGS = {
    "NumberField": re.compile(r"\bNumberField\b"),
    "IsCMField": re.compile(r"\bIsCMField\b"),
    "IsTotallyReal": re.compile(r"\bIsTotallyReal\b"),
    "IsTotallyComplex": re.compile(r"\bIsTotallyComplex\b"),
    "HeckeCharacter": re.compile(r"\bHeckeCharacter\b"),
    "dedekindZeta": re.compile(r"\b(dedekindZeta|completedDedekindZeta|continuedDedekindZeta|normalizedDedekindZeta)\b"),
    "DirichletCharacter": re.compile(r"\bDirichletCharacter\b"),
    "CyclotomicField": re.compile(r"\bCyclotomicField\b"),
    "riemannZeta": re.compile(r"\briemannZeta\b"),
    "D7_or_FamP": re.compile(r"\b(D7|FamP)\b"),
    "LocalField_or_Padic": re.compile(r"\b(IsNonarchimedeanLocalField|Padic|PadicAlgCl|Fontaine|Bcris|Prismatic|Wach)\b|ℚ_\[|ℂ_\[|ℤ_\["),
    "Scheme_or_Arakelov": re.compile(r"\b(Scheme|AlgebraicGeometry|Arakelov|Toroidal|Hironaka|Resolution|Principalisation|Moriwaki|Kawamata|Nadel|Ohsawa|Grothendieck)\b"),
    "LieGroup_or_Harmonic": re.compile(r"\b(HarishChandra|DiscreteSeries|BesselMap|Bessel|Poincare|SchwartzMap|HaarMeasure|IsHaarMeasure|Whittaker|Metaplectic|WeilRep|Fock)\b"),
    "GaloisCohomology": re.compile(r"\b(PoitouTate|ProfiniteCohomology|TateCohomology|BlochKato|Selmer|shaLen|GaloisCohomology)\b"),
}


def process_batch(rel_paths):
    res = {
        "top": defaultdict(lambda: Counter()),
        "sub": defaultdict(lambda: Counter()),
        "sub3": defaultdict(lambda: Counter()),
        "total": Counter(),
        "tags": Counter(),
        "tags_by_top": defaultdict(lambda: Counter()),
        "sorry_files": [],
        "erh_hits": [],
    }
    for rel in rel_paths:
        full = os.path.join(SRC_ROOT, rel)
        parts = rel.split("/")
        top = parts[0] if len(parts) > 1 else "(root)"
        sub = "/".join(parts[:2]) if len(parts) > 2 else top
        sub3 = "/".join(parts[:3]) if len(parts) > 3 else sub

        try:
            with open(full, "r", encoding="utf-8", errors="replace") as f:
                text = f.read()
        except Exception:
            continue

        n_bytes = len(text.encode("utf-8", errors="replace"))
        lines = text.splitlines()
        n_lines = len(lines)
        n_nonblank = sum(1 for ln in lines if ln.strip())

        n_thm = 0
        n_def = 0
        for ln in lines:
            m = RE_DECL.match(ln)
            if m:
                k = m.group(1)
                if k in ("theorem", "lemma"):
                    n_thm += 1
                else:
                    n_def += 1

        if RE_SORRY.search(text):
            # Exclude Challenge.lean comments or check actual
            res["sorry_files"].append(rel)

        # Tier classification (strict precedence A1 > A2 > B > C > D)
        has_a1 = bool(PAT_A1.search(text))
        has_a2 = bool(PAT_A2.search(text))
        has_b = bool(PAT_B.search(text))
        has_c = bool(PAT_C.search(text))

        if has_a1:
            tier = "A1_Q_HARDCODED"
        elif has_a2:
            tier = "A2_D7_FAMP_WRAPPER"
        elif has_b:
            tier = "B_CM_TC_TR_POLY"
        elif has_c:
            tier = "C_NF_POLY"
        else:
            tier = "D_FIELD_AGNOSTIC"

        for bucket in (res["total"], res["top"][top], res["sub"][sub], res["sub3"][sub3]):
            bucket["files"] += 1
            bucket["lines"] += n_lines
            bucket["nonblank"] += n_nonblank
            bucket["bytes"] += n_bytes
            bucket["thms"] += n_thm
            bucket["defs"] += n_def
            bucket[f"files_{tier}"] += 1
            bucket[f"lines_{tier}"] += n_lines
            # Also track independent presence
            if has_a1:
                bucket["has_a1_files"] += 1
            if has_a2:
                bucket["has_a2_files"] += 1
            if has_b:
                bucket["has_b_files"] += 1
            if has_c:
                bucket["has_c_files"] += 1

        for tname, pat in SPECIFIC_TAGS.items():
            if pat.search(text):
                res["tags"][f"files_{tname}"] += 1
                res["tags"][f"lines_{tname}"] += n_lines
                res["tags_by_top"][top][f"files_{tname}"] += 1
                res["tags_by_top"][top][f"lines_{tname}"] += n_lines

        if "extendedRiemann" in text or "ExtendedRiemann" in text or "dedekindZeta" in text:
            res["erh_hits"].append((rel, n_lines, tier))

    # Convert defaultdicts for pickling
    res["top"] = {k: dict(v) for k, v in res["top"].items()}
    res["sub"] = {k: dict(v) for k, v in res["sub"].items()}
    res["sub3"] = {k: dict(v) for k, v in res["sub3"].items()}
    res["tags_by_top"] = {k: dict(v) for k, v in res["tags_by_top"].items()}
    res["total"] = dict(res["total"])
    res["tags"] = dict(res["tags"])
    return res


def merge_counters(dst, src):
    for k, v in src.items():
        dst[k] = dst.get(k, 0) + v


def main():
    all_files = []
    for root, dirs, files in os.walk(SRC_ROOT):
        for fn in files:
            if fn.endswith(".lean"):
                rel = os.path.relpath(os.path.join(root, fn), SRC_ROOT)
                all_files.append(rel)
    all_files.sort()
    print(f"Found {len(all_files)} .lean files under {SRC_ROOT}", file=sys.stderr)

    n_workers = min(os.cpu_count() or 8, 12)
    chunk_size = max(1, (len(all_files) + n_workers * 4 - 1) // (n_workers * 4))
    batches = [all_files[i : i + chunk_size] for i in range(0, len(all_files), chunk_size)]

    merged = {
        "total": {},
        "top": defaultdict(dict),
        "sub": defaultdict(dict),
        "sub3": defaultdict(dict),
        "tags": {},
        "tags_by_top": defaultdict(dict),
        "sorry_files": [],
        "erh_hits": [],
    }

    with ProcessPoolExecutor(max_workers=n_workers) as ex:
        for part in ex.map(process_batch, batches):
            merge_counters(merged["total"], part["total"])
            merge_counters(merged["tags"], part["tags"])
            for k, v in part["top"].items():
                merge_counters(merged["top"][k], v)
            for k, v in part["sub"].items():
                merge_counters(merged["sub"][k], v)
            for k, v in part["sub3"].items():
                merge_counters(merged["sub3"][k], v)
            for k, v in part["tags_by_top"].items():
                merge_counters(merged["tags_by_top"][k], v)
            merged["sorry_files"].extend(part["sorry_files"])
            merged["erh_hits"].extend(part["erh_hits"])

    merged["top"] = dict(merged["top"])
    merged["sub"] = dict(merged["sub"])
    merged["sub3"] = dict(merged["sub3"])
    merged["tags_by_top"] = dict(merged["tags_by_top"])

    out_path = "erh_research/scripts/lean_polymorphism_audit.json"
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(merged, f, indent=2)

    T = merged["total"]
    print(f"\n=== TOTAL ARCHIVE ===")
    print(f"Files: {T['files']:,} | Lines: {T['lines']:,} | Non-blank: {T['nonblank']:,} | Bytes: {T['bytes']:,}")
    print(f"Theorems/Lemmas: {T['thms']:,} | Defs/Structs/Insts: {T['defs']:,}")
    print(f"Files containing 'sorry'/'admit' word: {len(merged['sorry_files'])} -> {merged['sorry_files'][:10]}")
    print(f"\n=== TIER BREAKDOWN (ALL {T['files']:,} FILES) ===")
    for tier in ["A1_Q_HARDCODED", "A2_D7_FAMP_WRAPPER", "B_CM_TC_TR_POLY", "C_NF_POLY", "D_FIELD_AGNOSTIC"]:
        fc = T.get(f"files_{tier}", 0)
        lc = T.get(f"lines_{tier}", 0)
        print(f"  {tier:22s}: {fc:7,d} files ({100*fc/T['files']:5.2f}%) | {lc:10,d} lines ({100*lc/T['lines']:5.2f}%)")

    gen_f = sum(T.get(f"files_{t}", 0) for t in ("B_CM_TC_TR_POLY", "C_NF_POLY", "D_FIELD_AGNOSTIC"))
    gen_l = sum(T.get(f"lines_{t}", 0) for t in ("B_CM_TC_TR_POLY", "C_NF_POLY", "D_FIELD_AGNOSTIC"))
    print(f"  --> TOTAL GENERAL (B+C+D): {gen_f:7,d} files ({100*gen_f/T['files']:5.2f}%) | {gen_l:10,d} lines ({100*gen_l/T['lines']:5.2f}%)")

    print(f"\n=== BY TOP-LEVEL LIBRARY ===")
    for k, v in sorted(merged["top"].items(), key=lambda kv: -kv[1]["lines"]):
        f_tot = v["files"]
        l_tot = v["lines"]
        l_gen = sum(v.get(f"lines_{t}", 0) for t in ("B_CM_TC_TR_POLY", "C_NF_POLY", "D_FIELD_AGNOSTIC"))
        l_a1 = v.get("lines_A1_Q_HARDCODED", 0)
        l_a2 = v.get("lines_A2_D7_FAMP_WRAPPER", 0)
        print(f"  {k:20s}: {f_tot:7,d} files | {l_tot:10,d} lines | A1={100*l_a1/l_tot:5.1f}% A2={100*l_a2/l_tot:5.1f}% GEN(B+C+D)={100*l_gen/l_tot:5.1f}%")


if __name__ == "__main__":
    main()
