#!/usr/bin/env python3
"""
Wave-3 Agent A19: Exact Lean 4.33.1 Bucket-Split Graph Analyzer & Zero-Cycle Simulator
over the full 164,464-module / 670,269-edge internal import DAG of riemann-hypothesis/src/.

READ-ONLY over riemann-hypothesis/src/ and tools/lean_index.db.

Features:
  1. Reproduces Track 17 v3 exact baseline (44,728 files / 4,856,043 lines = 29.28%).
  2. Runs v4 Precision Calibration catching 3 exact regex false positives in v3:
       (FP-1) `Module.finrank ℚ X = 2 * ...` (arbitrary totally complex / CM fields)
       (FP-2) 58 non-D7 local structures named `HidaSetting` (e.g. Formalism.REAL.HidaSetting,
              Formalism.MainNotions.V.Pf.V2.Calc.HidaSetting (k : ℕ))
       (FP-3) Pure complex-lattice Eisenstein series `ExistsVariableChangeEqLatticeCurve.lean`
  3. Separately measures Variant-II Native ERH mode where `Tor.Host E` (TwoWeightEqOneAddRoot.lean,
     which requires ONLY `[IsCMField E]` + `d % 16 = 7` + `sqrt(-d) ∈ O_E` + `Unramified`,
     with ZERO `[IsAbelianGalois ℚ E]`) is natively instantiated by `RelCMHostVariantII.toTorHost`.
  4. Runs exact bitmask TaintBoundary(w) computation and multi-strategy greedy bucket-split
     optimization for top k = 5, 10, 15, 25, 50, 100 bucket files.
  5. Explicitly constructs the split graph G_K (splitting each u ∈ K into u__Pure and u__Taint
     with edge u__Taint -> u__Pure and rewiring pure consumers to u__Pure), proves ZERO circular
     imports via Kahn's topological sort, and independently certifies exact transitive purity via BFS.
  6. Extracts exact TaintBoundary sets for 14 ERH landmark modules.
"""

import json
import os
import re
import sqlite3
import sys
import time
from collections import Counter, defaultdict, deque
from concurrent.futures import ProcessPoolExecutor

REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
SRC_ROOT = os.path.join(REPO_ROOT, "riemann-hypothesis", "src")
DB_PATH = os.path.join(REPO_ROOT, "tools", "lean_index.db")
CACHE_PATH = os.path.join(os.path.dirname(__file__), "w3_mod_cache.json")
V4_CACHE_PATH = os.path.join(os.path.dirname(__file__), "w3_mod_cache_v4.json")
OUT_JSON = os.path.join(os.path.dirname(__file__), "w3_bucket_split_results.json")

sys.path.insert(0, os.path.dirname(__file__))
import audit_transitive_dag_v3 as v3

PAT_FINRANK2_BAD = re.compile(r"Module\.finrank\s+ℚ\s+\w+\s*=\s*2\s*[\*\^]")
PAT_A1_V4 = re.compile(
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
    r"Module\.finrank\s+ℚ\s+\w+\s*=\s*2(?!\s*[\*\^0-9])"
)

PAT_A2_V4 = re.compile(
    r"\b("
    r"D7|FamP|FamCore|FamClass|SizeData₂|HostAx|HostRaw|Formalism\.BasicNotions\.Host|"
    r"ArithData|HostFacts|HostFactsS|TopG|VWin|VWinAt|VAt|HypV|LinkN|LinkV|LinkG|LinkS|LinkDIV|LinkMu|"
    r"PoincareSetting|TheoremSSelected|StepThmBG|HypsAlt|CovolumeBoundOfX|"
    r"BoundAtTwoThree|At23|IntInert|JetsInert|IntFirst|GoodOrigin|RootTower|Tor\.Host|"
    r"HostNumbers|hostRd|hostLval|Formalism\.L2\.SG\.HidaSetting"
    r")\b"
)

V4_EXTRA_EISENSTEIN_WHITELIST = (
    "Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsVariableChangeEqLatticeCurve.lean",
)

# Variant-II native Tor.Host files: TwoWeightEqOneAddRoot.lean itself plus files whose ONLY
# A2/A1 hit is Tor.Host (with zero IsAbelianGalois ℚ, D7, HostAx, etc.).
TOR_HOST_MOD = (
    "ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry."
    "ToroidalCompactification.TwoWeightEqOneAddRoot"
)

PAT_A2_NO_TORHOST = re.compile(
    r"\b("
    r"D7|FamP|FamCore|FamClass|SizeData₂|HostAx|HostRaw|Formalism\.BasicNotions\.Host|"
    r"ArithData|HostFacts|HostFactsS|TopG|VWin|VWinAt|VAt|HypV|LinkN|LinkV|LinkG|LinkS|LinkDIV|LinkMu|"
    r"PoincareSetting|TheoremSSelected|StepThmBG|HypsAlt|CovolumeBoundOfX|"
    r"BoundAtTwoThree|At23|IntInert|JetsInert|IntFirst|GoodOrigin|RootTower|"
    r"HostNumbers|hostRd|hostLval|Formalism\.L2\.SG\.HidaSetting"
    r")\b"
)


def reaudit_v4_batch(items):
    """Re-classify v3 A1/A2 modules under v4 precision rules + Variant-II Tor.Host check."""
    out = []
    for mod, rel, nl, tr, tc, cmo in items:
        full = os.path.join(SRC_ROOT, rel)
        with open(full, "r", encoding="utf-8", errors="replace") as f:
            text = f.read()
        text_nb = v3.PAT_CMSTAR_ATTR.sub("", text)

        a1 = bool(PAT_A1_V4.search(text))
        if not a1 and v3.PAT_PCHAR_HC.search(text):
            if (
                not rel.startswith("Formalism/RealPlaceAnalysis/")
                and "Formalism.REAL.PChar" not in text
                and "inP ε X" not in text
            ):
                a1 = True
        if (
            not a1
            and not rel.startswith(v3.AUX_NF_WHITELIST_PREFIXES)
            and rel not in V4_EXTRA_EISENSTEIN_WHITELIST
        ):
            if v3.PAT_RIEMANN_ZETA.search(text) or v3.PAT_CYC_Q.search(text):
                a1 = True

        a2 = (not a1) and (
            bool(PAT_A2_V4.search(text_nb))
            or ("SiegelLatticeTheory.HaarTransversals.HidaSetting" in text_nb)
        )

        # Tier under v4 (after stripping Host.cmStar boilerplate)
        if a1:
            t_v4 = "A1"
        elif a2:
            t_v4 = "A2"
        elif v3.PAT_B.search(text_nb):
            t_v4 = "B"
        elif v3.PAT_C.search(text_nb):
            t_v4 = "C"
        else:
            t_v4 = "D"

        # Check if Tor.Host-only (Variant-II native)
        tor_only = False
        if mod == TOR_HOST_MOD:
            tor_only = True
        elif t_v4 == "A2" and not PAT_A2_NO_TORHOST.search(text_nb) and (
            "SiegelLatticeTheory.HaarTransversals.HidaSetting" not in text_nb
        ):
            tor_only = True

        fp_tag = None
        if tc == "A1" and t_v4 != "A1":
            if rel in V4_EXTRA_EISENSTEIN_WHITELIST:
                fp_tag = "FP_EISENSTEIN_ZETA"
            elif PAT_FINRANK2_BAD.search(text):
                fp_tag = "FP_FINRANK2_MUL"
            else:
                fp_tag = "FP_A1_OTHER"
        elif tc == "A2" and t_v4 not in ("A1", "A2"):
            fp_tag = "FP_HIDASETTING"

        out.append((mod, t_v4, 1 if tor_only else 0, fp_tag))
    return out


def build_or_load_v4_cache(v3_cache):
    if os.path.exists(V4_CACHE_PATH):
        with open(V4_CACHE_PATH, "r", encoding="utf-8") as f:
            return json.load(f)

    a_items = [
        (m, v[0], v[1], v[2], v[3], v[4])
        for m, v in v3_cache.items()
        if v[2] in ("A1", "A2")
    ]
    n_workers = min(os.cpu_count() or 8, 12)
    chunk = max(1, (len(a_items) + n_workers * 4 - 1) // (n_workers * 4))
    batches = [a_items[i : i + chunk] for i in range(0, len(a_items), chunk)]

    v4_updates = {}
    fp_counts = Counter()
    fp_lines = Counter()
    fp_samples = defaultdict(list)

    with ProcessPoolExecutor(max_workers=n_workers) as ex:
        for part in ex.map(reaudit_v4_batch, batches):
            for mod, t_v4, tor_only, fp_tag in part:
                v4_updates[mod] = [t_v4, tor_only, fp_tag]
                if fp_tag:
                    fp_counts[fp_tag] += 1
                    fp_lines[fp_tag] += v3_cache[mod][1]
                    if len(fp_samples[fp_tag]) < 10:
                        fp_samples[fp_tag].append(v3_cache[mod][0])

    data = {
        "updates": v4_updates,
        "fp_counts": dict(fp_counts),
        "fp_lines": dict(fp_lines),
        "fp_samples": dict(fp_samples),
    }
    with open(V4_CACHE_PATH, "w", encoding="utf-8") as f:
        json.dump(data, f)
    return data


def load_graph(mod_set):
    conn = sqlite3.connect(DB_PATH)
    fwd = defaultdict(set)
    rev = defaultdict(set)
    self_loops = []
    for m, imp in conn.execute("SELECT module, imported FROM imports"):
        if m in mod_set and imp in mod_set:
            if m == imp:
                self_loops.append(m)
            else:
                fwd[m].add(imp)
                rev[imp].add(m)
    conn.close()

    # Topological sort (imports first)
    indeg = {m: len(fwd[m]) for m in mod_set}
    q = deque([m for m, d in indeg.items() if d == 0])
    topo = []
    while q:
        u = q.popleft()
        topo.append(u)
        for v in rev[u]:
            indeg[v] -= 1
            if indeg[v] == 0:
                q.append(v)
    assert len(topo) == len(mod_set), f"Graph not a DAG! {len(topo)} != {len(mod_set)}"
    return fwd, rev, topo, self_loops


def compute_taint_boundaries(topo, fwd, P, S):
    """Exact bitmask TaintBoundary(w) for all w in P."""
    B_cand = sorted({imp for v in P for imp in fwd[v] if imp in S})
    b_bit = {u: 1 << i for i, u in enumerate(B_cand)}
    TB = {}
    for m in topo:
        if m in P:
            mask = 0
            for imp in fwd[m]:
                if imp in S:
                    mask |= b_bit[imp]
                else:
                    mask |= TB[imp]
            TB[m] = mask
    return B_cand, TB


def verify_split_dag_zero_cycles(mod_set, fwd, P, S, split_set, mod_lines, TB=None, b_idx=None):
    """
    Explicitly construct TWO rewired split graphs G_K:
      (1) Exact-split G_K: each u in K is split into (u,'P') and (u,'T') with (u,'T') -> (u,'P');
          pure consumers w in P rewire (w -> u) to (w -> (u,'P')); (u,'P') imports ONLY those
          v in fwd[u] ∩ P that are themselves pure under K (plus (u','P') for u' in fwd[u] ∩ K),
          while any transitively-tainted import of u stays on (u,'T').
      (2) Conservative-split G_K^cons: (u,'P') blindly inherits ALL v in fwd[u] ∩ P (even if v
          itself transitively depends on S \\ K).
    Proves ZERO circular imports on BOTH via Kahn's topological sort AND independently counts
    exact transitively-pure original nodes in P via reverse BFS from all taint seeds.
    """
    split_set = set(split_set)
    k_mask = 0
    if b_idx is not None:
        for u in split_set:
            if u in b_idx:
                k_mask |= 1 << b_idx[u]

    def build_and_check(conservative: bool):
        nodes = set()
        g_fwd = defaultdict(set)
        g_rev = defaultdict(set)

        def add_edge(a, b):
            if a != b:
                g_fwd[a].add(b)
                g_rev[b].add(a)

        for m in mod_set:
            if m in split_set:
                nodes.add((m, "P"))
                nodes.add((m, "T"))
                add_edge((m, "T"), (m, "P"))
            else:
                nodes.add((m, "O"))

        for m in mod_set:
            if m in P:
                src = (m, "O")
                for imp in fwd[m]:
                    dst = (imp, "P") if imp in split_set else (imp, "O")
                    add_edge(src, dst)
            elif m in split_set:
                src_p = (m, "P")
                src_t = (m, "T")
                for imp in fwd[m]:
                    if imp in P:
                        if conservative or TB is None or ((TB[imp] & ~k_mask) == 0):
                            add_edge(src_p, (imp, "O"))
                        else:
                            add_edge(src_t, (imp, "O"))
                    elif imp in split_set:
                        add_edge(src_p, (imp, "P"))
                        add_edge(src_t, (imp, "T"))
                    else:
                        add_edge(src_t, (imp, "O"))
            else:
                src = (m, "O")
                for imp in fwd[m]:
                    dst = (imp, "T") if imp in split_set else (imp, "O")
                    add_edge(src, dst)

        indeg = {n: len(g_fwd[n]) for n in nodes}
        q = deque([n for n, d in indeg.items() if d == 0])
        visited_topo = 0
        while q:
            u = q.popleft()
            visited_topo += 1
            for v in g_rev[u]:
                indeg[v] -= 1
                if indeg[v] == 0:
                    q.append(v)
        cycles = len(nodes) - visited_topo

        taint_seeds = [(m, "O") for m in (S - split_set)] + [(u, "T") for u in split_set]
        tainted = set(taint_seeds)
        q = deque(taint_seeds)
        while q:
            u = q.popleft()
            for v in g_rev[u]:
                if v not in tainted:
                    tainted.add(v)
                    q.append(v)

        pure_orig = [m for m in P if (m, "O") not in tainted]
        return len(nodes), cycles, len(pure_orig), sum(mod_lines[m] for m in pure_orig)

    n_tot, cyc_ex, pf_ex, pl_ex = build_and_check(conservative=False)
    _, cyc_co, pf_co, pl_co = build_and_check(conservative=True)
    return {
        "split_nodes_total": n_tot,
        "cycles": cyc_ex,
        "cycles_conservative": cyc_co,
        "pure_files": pf_ex,
        "pure_lines": pl_ex,
        "conservative_pure_files": pf_co,
        "conservative_pure_lines": pl_co,
    }


def optimize_bucket_splits(B_cand, TB, P, mod_lines, mod_rel, max_k=100, power=2.0):
    """
    Exact O(sum |TB|) Incremental Inverted-Index Harmonic-Weighted Greedy Bucket-Split Optimizer.
    Maintains exact scores[i] incrementally: when bit `best_idx` is chosen, ONLY the compressed
    bitmask groups containing `best_idx` are updated. Produces bit-for-bit identical decisions
    to full recomputation, 50x faster.
    Special case power=None: pure immediate-unlock greedy (with p=2.0 tie-break when imm=0).
    """
    base_pure_f = sum(1 for m in P if TB[m] == 0)
    base_pure_l = sum(mod_lines[m] for m in P if TB[m] == 0)

    mask_files = Counter()
    mask_lines = Counter()
    for m in P:
        mk = TB[m]
        if mk != 0:
            mask_files[mk] += 1
            mask_lines[mk] += mod_lines[m]

    n_B = len(B_cand)
    # groups[g_id] = [rem_mask, bit_count, n_files, n_lines, current_weight_per_bit]
    groups = []
    inv_idx = [[] for _ in range(n_B)]
    scores = [0.0] * n_B
    imm_l = [0] * n_B

    eff_p = 2.0 if power is None else power

    def weight_of(nl, bc):
        if bc == 1:
            return float(nl)
        return nl / (bc ** eff_p)

    for g_id, mk in enumerate(mask_files):
        nf = mask_files[mk]
        nl = mask_lines[mk]
        bc = mk.bit_count()
        w = weight_of(nl, bc)
        groups.append([mk, bc, nf, nl, w])
        if bc == 1:
            idx = mk.bit_length() - 1
            imm_l[idx] += nl
        x = mk
        while x:
            lsb = x & -x
            idx = lsb.bit_length() - 1
            inv_idx[idx].append(g_id)
            scores[idx] += w
            x ^= lsb

    chosen = []
    chosen_set = set()
    cur_f = base_pure_f
    cur_l = base_pure_l

    for step in range(1, min(max_k, n_B) + 1):
        if power is None:
            best_idx = max(
                (i for i in range(n_B) if i not in chosen_set),
                key=lambda i: (imm_l[i], scores[i]),
            )
            if imm_l[best_idx] == 0 and scores[best_idx] <= 0:
                break
        else:
            best_idx = max(
                (i for i in range(n_B) if i not in chosen_set),
                key=lambda i: (scores[i], imm_l[i]),
            )
            if scores[best_idx] <= 0:
                break

        chosen_set.add(best_idx)
        bit = 1 << best_idx
        inv_bit = ~bit
        unlocked_f = 0
        unlocked_l = 0

        for g_id in inv_idx[best_idx]:
            g = groups[g_id]
            rem = g[0]
            if not (rem & bit):
                continue
            old_bc = g[1]
            nf = g[2]
            nl = g[3]
            old_w = g[4]
            if old_bc == 1:
                imm_l[best_idx] -= nl
                scores[best_idx] -= old_w
                g[0] = 0
                g[1] = 0
                g[4] = 0.0
                unlocked_f += nf
                unlocked_l += nl
            else:
                new_rem = rem & inv_bit
                new_bc = old_bc - 1
                new_w = weight_of(nl, new_bc)
                delta_w = new_w - old_w
                scores[best_idx] -= old_w
                g[0] = new_rem
                g[1] = new_bc
                g[4] = new_w
                if new_bc == 1:
                    idx = new_rem.bit_length() - 1
                    imm_l[idx] += nl
                    scores[idx] += delta_w
                else:
                    x = new_rem
                    while x:
                        lsb = x & -x
                        scores[lsb.bit_length() - 1] += delta_w
                        x ^= lsb

        cur_f += unlocked_f
        cur_l += unlocked_l
        chosen.append(
            {
                "step": step,
                "module": B_cand[best_idx],
                "rel_path": mod_rel[B_cand[best_idx]],
                "step_unlocked_files": unlocked_f,
                "step_unlocked_lines": unlocked_l,
                "cum_pure_files": cur_f,
                "cum_pure_lines": cur_l,
            }
        )
    return base_pure_f, base_pure_l, chosen


def run_regime(name, mod_set, topo, fwd, rev, P, S, mod_lines, mod_rel, total_lines):
    t0 = time.time()
    B_cand, TB = compute_taint_boundaries(topo, fwd, P, S)
    base_f = sum(1 for m in P if TB[m] == 0)
    base_l = sum(mod_lines[m] for m in P if TB[m] == 0)
    p_total_f = len(P)
    p_total_l = sum(mod_lines[m] for m in P)

    print(f"\n{'=' * 78}")
    print(f"REGIME: {name}")
    print(f"{'=' * 78}")
    print(
        f"Direct Clean Pure |P| = {p_total_f:,} f ({p_total_l:,} L, {100*p_total_l/total_lines:.2f}%) | "
        f"|S| = {len(S):,} f | |B_cand| = {len(B_cand):,}"
    )
    print(
        f"0-Split Trans-Pure    = {base_f:,} f ({base_l:,} L, {100*base_l/total_lines:.2f}%) | "
        f"Locked = {p_total_f - base_f:,} f ({p_total_l - base_l:,} L)"
    )

    # Compare powers p = 1.0, 1.5, 2.0, 3.0, None (pure immediate-unlock greedy)
    best_by_p = {}
    for p in (1.0, 1.5, 2.0, 3.0, None):
        _, _, ch = optimize_bucket_splits(B_cand, TB, P, mod_lines, mod_rel, max_k=100, power=p)
        best_by_p[p] = ch
        m5 = ch[4]["cum_pure_lines"] if len(ch) >= 5 else base_l
        m10 = ch[9]["cum_pure_lines"] if len(ch) >= 10 else base_l
        m15 = ch[14]["cum_pure_lines"] if len(ch) >= 15 else base_l
        m25 = ch[24]["cum_pure_lines"] if len(ch) >= 25 else base_l
        m50 = ch[49]["cum_pure_lines"] if len(ch) >= 50 else base_l
        m100 = ch[99]["cum_pure_lines"] if len(ch) >= 100 else base_l
        plab = "imm" if p is None else f"{p:3.1f}"
        print(
            f"  [p={plab}] k=5:{100*m5/total_lines:5.2f}% | k=10:{100*m10/total_lines:5.2f}% | "
            f"k=15:{100*m15/total_lines:5.2f}% | k=25:{100*m25/total_lines:5.2f}% | "
            f"k=50:{100*m50/total_lines:5.2f}% | k=100:{100*m100/total_lines:5.2f}%"
        )

    # Select power maximizing k=25 (break ties at k=15)
    best_p = max(
        best_by_p.keys(),
        key=lambda p: (
            best_by_p[p][24]["cum_pure_lines"],
            best_by_p[p][14]["cum_pure_lines"],
        ),
    )
    chosen = best_by_p[best_p]
    print(f"  --> Best optimizer power: p={best_p}")

    # Verify zero circular imports + exact BFS match at k = 5, 10, 15, 25!
    b_idx = {u: i for i, u in enumerate(B_cand)}
    verifications = {}
    for k in (5, 10, 15, 25):
        K_mods = [c["module"] for c in chosen[:k]]
        ver = verify_split_dag_zero_cycles(mod_set, fwd, P, S, K_mods, mod_lines, TB=TB, b_idx=b_idx)
        assert ver["cycles"] == 0 and ver["cycles_conservative"] == 0, f"CYCLES DETECTED at k={k}!"
        assert ver["pure_files"] == chosen[k - 1]["cum_pure_files"], (
            f"File mismatch at k={k}: {ver['pure_files']} vs {chosen[k-1]['cum_pure_files']}"
        )
        assert ver["pure_lines"] == chosen[k - 1]["cum_pure_lines"], "Line mismatch!"
        verifications[str(k)] = ver
        delta_f = ver["pure_files"] - base_f
        delta_l = ver["pure_lines"] - base_l
        print(
            f"  [VERIFIED DAG k={k:2d}] 0 cycles (|V(G_K)|={ver['split_nodes_total']:,}) | "
            f"Exact={ver['pure_files']:,} f ({ver['pure_lines']:,} L, {100*ver['pure_lines']/total_lines:.2f}%, +{delta_l:,} L) | "
            f"Cons={ver['conservative_pure_files']:,} f ({100*ver['conservative_pure_lines']/total_lines:.2f}%)"
        )

    print(f"\n  Top 25 Selected Bucket Files (p={best_p}):")
    for c in chosen[:25]:
        print(
            f"   {c['step']:2d}. +{c['step_unlocked_files']:5,d} f (+{c['step_unlocked_lines']:9,d} L) "
            f"-> {100*c['cum_pure_lines']/total_lines:5.2f}% | {c['rel_path']}"
        )

    print(f"  (Completed regime in {time.time()-t0:.2f}s)")
    return {
        "name": name,
        "direct_pure_files": p_total_f,
        "direct_pure_lines": p_total_l,
        "boundary_count": len(B_cand),
        "zero_split_files": base_f,
        "zero_split_lines": base_l,
        "best_power": best_p,
        "milestones_all_powers": {
            str(p): {
                str(k): {
                    "files": ch[k - 1]["cum_pure_files"],
                    "lines": ch[k - 1]["cum_pure_lines"],
                    "pct_lines": round(100 * ch[k - 1]["cum_pure_lines"] / total_lines, 3),
                }
                for k in (5, 10, 15, 25, 50, 100)
                if len(ch) >= k
            }
            for p, ch in best_by_p.items()
        },
        "verifications": verifications,
        "top25": chosen[:25],
        "top50_summary": [
            {
                "step": c["step"],
                "rel_path": c["rel_path"],
                "step_unlocked_lines": c["step_unlocked_lines"],
                "cum_pure_lines": c["cum_pure_lines"],
            }
            for c in chosen[:50]
        ],
    }


def main():
    t_start = time.time()
    with open(CACHE_PATH, "r", encoding="utf-8") as f:
        v3_cache = json.load(f)

    mod_rel = {m: v[0] for m, v in v3_cache.items()}
    mod_lines = {m: v[1] for m, v in v3_cache.items()}
    mod_raw = {m: v[2] for m, v in v3_cache.items()}
    mod_clean_v3 = {m: v[3] for m, v in v3_cache.items()}
    mod_set = set(v3_cache.keys())
    total_lines = sum(mod_lines.values())

    print(f"Loaded {len(mod_set):,} modules ({total_lines:,} lines).")
    fwd, rev, topo, self_loops = load_graph(mod_set)
    print(f"Verified exact DAG: {len(topo):,} / {len(mod_set):,} modules, 0 cycles (filtered {len(self_loops)} comment self-loop: {self_loops}).")

    # 1. Exact v3 RAW baseline check
    S_raw = {m for m in mod_set if mod_raw[m] in ("A1", "A2")}
    P_raw = mod_set - S_raw
    ver_raw = verify_split_dag_zero_cycles(mod_set, fwd, P_raw, S_raw, [], mod_lines)
    print(
        f"\n[BASELINE Track 17 v3 RAW] Trans-Pure = {ver_raw['pure_files']:,} files / "
        f"{ver_raw['pure_lines']:,} lines ({100*ver_raw['pure_lines']/total_lines:.2f}%)"
    )

    # 2. v4 Precision Calibration
    v4_data = build_or_load_v4_cache(v3_cache)
    print("\n=== v4 PRECISION CALIBRATION: FALSE POSITIVES IN Track 17 v3 ===")
    for k, cnt in sorted(v4_data["fp_counts"].items()):
        print(f"  {k:22s}: {cnt:6,d} files ({v4_data['fp_lines'][k]:9,d} lines)")
        print(f"    samples: {v4_data['fp_samples'][k][:5]}")

    mod_v4 = {}
    tor_only_mods = set()
    for m in mod_set:
        if m in v4_data["updates"]:
            t_v4, tor_only, _ = v4_data["updates"][m]
            mod_v4[m] = t_v4
            if tor_only:
                tor_only_mods.add(m)
        else:
            mod_v4[m] = mod_clean_v3[m]

    print(f"  Variant-II Native Tor.Host-only modules: {len(tor_only_mods):,} files ({sum(mod_lines[m] for m in tor_only_mods):,} lines)")

    # Run all 3 regimes
    # Regime 1: Track 17 v3 Clean (after stripping 3,253 Host.cmStar headers)
    P_v3 = {m for m in mod_set if mod_clean_v3[m] in ("B", "C", "D")}
    S_v3 = mod_set - P_v3
    r1 = run_regime("R1: Track 17 v3 Rules (Stripped cmStar)", mod_set, topo, fwd, rev, P_v3, S_v3, mod_lines, mod_rel, total_lines)

    # Regime 2: v4 Precision-Calibrated Strict Arbitrary-Number-Field Purity
    P_v4 = {m for m in mod_set if mod_v4[m] in ("B", "C", "D")}
    S_v4 = mod_set - P_v4
    r2 = run_regime("R2: v4 Precision-Calibrated (Strict NF Purity)", mod_set, topo, fwd, rev, P_v4, S_v4, mod_lines, mod_rel, total_lines)

    # Regime 3: v4 Precision-Calibrated + Variant-II Native Tor.Host
    P_v4_v2 = P_v4 | tor_only_mods
    S_v4_v2 = mod_set - P_v4_v2
    r3 = run_regime("R3: v4 Precision-Calibrated + Variant-II Native Tor.Host", mod_set, topo, fwd, rev, P_v4_v2, S_v4_v2, mod_lines, mod_rel, total_lines)

    # 4. Landmark ERH Module TaintBoundary Inspection (under R2 Strict v4 and R3 Variant-II)
    landmarks = [
        ("WeilTensorModels (ch14)", "Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels"),
        ("ThetaIntegralsAgree (ch14)", "Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree"),
        ("BesselMapUniqGapAlt (ch21)", "CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGapAlt"),
        ("RecTExists (ch32)", "Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists"),
        ("LemmaKOfLitN (ch27)", "Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfLitN"),
        ("DeligneRibetHolds (ch26/28)", "Development.WeilBound.CoreStatements.AutomorphicKernels.DeligneRibet.DeligneRibetHolds"),
        ("RowSrc / Row0b (ch31)", "Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.RowSrc"),
        ("TLiftK (ch31)", "Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.TLiftK"),
        ("GoodTowerExistsX (ch18)", "Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX"),
        ("AdmissibleMonoIdeal (ch29 Lemma M)", "Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.AdmissibleMonoIdeal"),
        ("EulerVanishingBelowDimension (HidaSetting k)", "Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerVanishingBelowDimension"),
        ("DedekindZetaContinuation (Tate)", "GroundTheory.GlobalFields.TateThesis.DedekindZetaContinuation"),
        ("HeckeTheoremFE (Tate)", "GroundTheory.GlobalFields.TateThesis.HeckeTheoremFE"),
        ("SiegelMassRatioCM (ch17)", "Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice"),
    ]
    B_v4, TB_v4 = compute_taint_boundaries(topo, fwd, P_v4, S_v4)
    B_v2, TB_v2 = compute_taint_boundaries(topo, fwd, P_v4_v2, S_v4_v2)

    print(f"\n{'=' * 78}")
    print("LANDMARK ERH MODULES: EXACT TAINT BOUNDARY AUDIT (R2 Strict v4 vs R3 Variant-II)")
    print(f"{'=' * 78}")
    landmark_report = []
    for label, mod in landmarks:
        if mod not in mod_set:
            print(f"  [MISSING] {label}: {mod}")
            continue
        in_p_v4 = mod in P_v4
        in_p_v2 = mod in P_v4_v2
        tb_list_v4 = []
        if in_p_v4:
            x = TB_v4[mod]
            while x:
                lsb = x & -x
                tb_list_v4.append(mod_rel[B_v4[lsb.bit_length() - 1]])
                x ^= lsb
        tb_list_v2 = []
        if in_p_v2:
            x = TB_v2[mod]
            while x:
                lsb = x & -x
                tb_list_v2.append(mod_rel[B_v2[lsb.bit_length() - 1]])
                x ^= lsb
        status_v4 = "PURE" if (in_p_v4 and not tb_list_v4) else (f"BLOCKED({len(tb_list_v4)})" if in_p_v4 else f"SELF-{mod_v4[mod]}")
        status_v2 = "PURE" if (in_p_v2 and not tb_list_v2) else (f"BLOCKED({len(tb_list_v2)})" if in_p_v2 else f"SELF-{mod_v4[mod]}")
        print(f"  {label:42s} | R2={status_v4:13s} | R3={status_v2:13s}")
        if tb_list_v2:
            for b in tb_list_v2[:5]:
                print(f"      blocker(R3): {b}")
        elif tb_list_v4:
            for b in tb_list_v4[:5]:
                print(f"      blocker(R2): {b}")
        landmark_report.append({
            "label": label,
            "module": mod,
            "rel_path": mod_rel[mod],
            "status_v4": status_v4,
            "status_v2": status_v2,
            "blockers_v4": tb_list_v4,
            "blockers_v2": tb_list_v2,
        })

    out = {
        "total_files": len(mod_set),
        "total_lines": total_lines,
        "baseline_v3_raw": ver_raw,
        "v4_false_positives": {
            "counts": v4_data["fp_counts"],
            "lines": v4_data["fp_lines"],
            "samples": v4_data["fp_samples"],
        },
        "tor_only_files": len(tor_only_mods),
        "tor_only_lines": sum(mod_lines[m] for m in tor_only_mods),
        "regimes": {"R1_v3": r1, "R2_v4_strict": r2, "R3_v4_variantII": r3},
        "landmarks": landmark_report,
    }
    with open(OUT_JSON, "w", encoding="utf-8") as f:
        json.dump(out, f, indent=2)
    print(f"\nSaved complete verified simulation results to {OUT_JSON} in {time.time()-t_start:.1f}s.")


if __name__ == "__main__":
    main()
