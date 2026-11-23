#!/usr/bin/env python3
"""
Wave-14 L01 Independent Symbolic & Finite-Instance Verification Script
for Pure Commutative Algebra Lemma K02-Q1 (Refutation of d-independent K02-Q1,
Sharp Optimal Constant c_opt(d) = floor(d/2), Distinct-Weight Bound (r^+-1)Phi + r^+ Phi^*,
and Exact Matlis Duality Four-Fold Dictionary).

Covers:
  Suite 1 (Theorem L01-1): Explicit 2n x 2n staircase counterexample family P_{n,k}
                           achieving exp(Q_1) = n*k = floor(d/2)*max(Phi, Phi^*)
                           with Phi = Phi^* = k (refuting c=1 at d=4, H=4 and any
                           d-independent constant c as n -> infty), plus odd rank d=2n+1.
  Suite 2 (Theorem L01-2): Exact length identities (*_-) and (*_+) verified to exact
                           equality on adversarial, staircase, non-triangular, and random
                           matrices (d=2..6, p in {2,3,5}), plus unconditional d=3 c=1 check.
  Suite 3 (Theorem L01-4): Distinct nonnegative-weight bound (r^+-1)Phi + r^+ Phi^* and
                           r^+=1 exact quotient bound exp(Q_1) <= Phi^*, plus explicit
                           two-weight witness showing r^-=1 fails exp(Q_1) <= r^- Phi.
  Suite 4 (Theorem L01-3): Direct computation of X_m = N_m^sat / N_m, ker/coker of (*E)
                           and (proj), exact invariant-factor verification of the 4-fold
                           Matlis duality dictionary, and sharp width bound min((M-1)Phi, (h+1)Phi^*).

DISCLAIMER (Iron Rule 5): This script checks symbolic formulas and finite matrix instances.
All general theorems are proved algebraically in erh_research/wave14/L01_prove_or_refute_k02_q1.md.
"""

import math
import random
import sympy as sp

E_sym = sp.Symbol("E")


def vp(x: int, p: int = 2) -> int:
    if x == 0:
        return 10**9
    v = 0
    x = abs(int(x))
    while x % p == 0:
        x //= p
        v += 1
    return v


def snf_p_invariants(A_int, p: int = 2):
    """Return sorted list of p-adic valuations of nonzero invariant factors of A_int over Z_(p)."""
    if not A_int or not A_int[0]:
        return []
    M = [[int(x) for x in row] for row in A_int]
    nrows, ncols = len(M), len(M[0])
    invs = []
    r0 = c0 = 0
    MOD = p**45
    while r0 < nrows and c0 < ncols:
        best_v = 10**9
        bi = bj = -1
        for i in range(r0, nrows):
            for j in range(c0, ncols):
                v = vp(M[i][j], p)
                if v < best_v:
                    best_v = v
                    bi, bj = i, j
                    if best_v == 0:
                        break
            if best_v == 0:
                break
        if best_v == 10**9:
            break
        M[r0], M[bi] = M[bi], M[r0]
        for i in range(nrows):
            M[i][c0], M[i][bj] = M[i][bj], M[i][c0]
        piv = M[r0][c0]
        u = piv // (p**best_v)
        for i in range(r0 + 1, nrows):
            if M[i][c0] != 0:
                q = M[i][c0] // (p**best_v)
                for j in range(c0, ncols):
                    M[i][j] = (u * M[i][j] - q * M[r0][j]) % MOD
        for j in range(c0 + 1, ncols):
            if M[r0][j] != 0:
                q = M[r0][j] // (p**best_v)
                for i in range(r0, nrows):
                    M[i][j] = (u * M[i][j] - q * M[i][c0]) % MOD
        invs.append(best_v)
        r0 += 1
        c0 += 1
    return sorted(invs)


def tors_invs(invs):
    """Filter nonzero p-adic invariant factors (the torsion part)."""
    return [v for v in invs if v > 0]


def exp_from_invs(invs) -> int:
    return max(invs) if invs else 0


def len_from_invs(invs) -> int:
    return sum(invs)


def p_sat_ker(A_list, p: int = 2):
    """Compute a Z_(p)-basis of ker_{Z_(p)}(A_list)."""
    A_sp = sp.Matrix(A_list)
    ns = A_sp.nullspace()
    if not ns:
        return []
    cols = []
    for v in ns:
        den = sp.lcm([sp.fraction(y)[1] for y in v])
        cols.append([int(x * den) for x in v])
    r = len(cols)
    m = len(cols[0])
    B = [list(c) for c in cols]
    while True:
        R = [[x % p for x in row] for row in B]
        ops = [[1 if i == j else 0 for j in range(r)] for i in range(r)]
        piv_row = 0
        for col in range(m):
            found = next((i for i in range(piv_row, r) if R[i][col] % p != 0), -1)
            if found == -1:
                continue
            R[piv_row], R[found] = R[found], R[piv_row]
            ops[piv_row], ops[found] = ops[found], ops[piv_row]
            inv = pow(R[piv_row][col], -1, p)
            R[piv_row] = [(x * inv) % p for x in R[piv_row]]
            ops[piv_row] = [(x * inv) % p for x in ops[piv_row]]
            for i in range(r):
                if i != piv_row and R[i][col] != 0:
                    f = R[i][col]
                    R[i] = [(R[i][j] - f * R[piv_row][j]) % p for j in range(m)]
                    ops[i] = [(ops[i][j] - f * ops[piv_row][j]) % p for j in range(r)]
            piv_row += 1
        if piv_row == r:
            break
        comb = ops[piv_row]
        idx = next(j for j in range(r) if comb[j] % p != 0)
        B[idx] = [sum(comb[j] * B[j][c] for j in range(r)) // p for c in range(m)]
    return B


def p_sat_span(vecs, p: int = 2):
    """Compute a Z_(p)-basis of the p-saturation of the Z_(p)-span of vecs (list of row-lists)."""
    if not vecs:
        return []
    M = sp.Matrix(vecs)
    # Extract linearly independent rows
    pivs = M.T.rref()[1]
    if not pivs:
        return []
    B = [list(vecs[i]) for i in pivs]
    r = len(B)
    m = len(B[0])
    while True:
        R = [[x % p for x in row] for row in B]
        ops = [[1 if i == j else 0 for j in range(r)] for i in range(r)]
        piv_row = 0
        for col in range(m):
            found = next((i for i in range(piv_row, r) if R[i][col] % p != 0), -1)
            if found == -1:
                continue
            R[piv_row], R[found] = R[found], R[piv_row]
            ops[piv_row], ops[found] = ops[found], ops[piv_row]
            inv = pow(R[piv_row][col], -1, p)
            R[piv_row] = [(x * inv) % p for x in R[piv_row]]
            ops[piv_row] = [(x * inv) % p for x in ops[piv_row]]
            for i in range(r):
                if i != piv_row and R[i][col] != 0:
                    f = R[i][col]
                    R[i] = [(R[i][j] - f * R[piv_row][j]) % p for j in range(m)]
                    ops[i] = [(ops[i][j] - f * ops[piv_row][j]) % p for j in range(r)]
            piv_row += 1
        if piv_row == r:
            break
        comb = ops[piv_row]
        idx = next(j for j in range(r) if comb[j] % p != 0)
        B[idx] = [sum(comb[j] * B[j][c] for j in range(r)) // p for c in range(m)]
    return B


def sublattice_quotient_invs(sub_vecs, super_basis, p: int = 2):
    """
    Given super_basis (list of r p-saturated vectors in Z^m) and sub_vecs (list of vectors
    lying in Z_(p)-span(super_basis)), return sorted nonzero SNF p-valuations of
    span(super_basis) / span(sub_vecs).
    """
    if not super_basis:
        return []
    if not sub_vecs:
        return None  # infinite quotient
    B_sp = sp.Matrix(super_basis).T  # m x r
    T_sp = sp.Matrix(sub_vecs).T     # m x s
    piv_rows = list(B_sp.T.rref()[1])
    B_sq = B_sp[piv_rows, :]
    T_sq = T_sp[piv_rows, :]
    X = B_sq.inv() * T_sq  # r x s, entries in Z_(p)
    # Clear any p'-denominators
    den = sp.lcm([sp.fraction(sp.together(X[i, j]))[1] for i in range(X.rows) for j in range(X.cols)])
    assert int(den) % p != 0, f"p divides denominator {den} in sublattice express!"
    X_int = [[int(X[i, j] * den) for j in range(X.cols)] for i in range(X.rows)]
    invs = snf_p_invariants(X_int, p)
    assert len(invs) == len(super_basis), "sub_vecs does not have full rank inside super_basis!"
    return invs


def build_Pn(n: int, p: int = 2, k: int = 1) -> sp.Matrix:
    """
    Explicit 2n x 2n upper-triangular staircase matrix P_{n,k} over Z_p[[E]].
    Basis order: e_1, ..., e_{n+1}, f_1, ..., f_{n-1}.
    """
    q = p**k
    d = 2 * n
    P = sp.zeros(d, d)
    P[0, 0] = E_sym ** (2 * n - 1)
    for j in range(1, n):
        P[j - 1, j] = q * E_sym ** (n - j)
        P[j, j] = E_sym ** (n - j)
    P[n - 1, n] = q
    P[n, n] = E_sym
    for r in range(1, n):
        col = n + r
        P[0, col] = (q ** (n - r)) * E_sym ** (n - 1 + r)
        P[col, col] = E_sym ** (n + r)
    return P


def compute_exact_data(P: sp.Matrix, p: int = 2):
    """
    For P in M_d(Z[E]) with E^H P^{-1} in M_d(Z_(p)[E]) (minimal H >= 1),
    compute full invariant factor profiles for L_1 = S^d, L_2 = P S^d:
      - H (minimal width)
      - Ps = E^H (P^{-1})^T
      - F_invs[k]  (k = 1..H): invariant factors of F_{-k}(L_1, L_2) -> C_{-k}(L_1, L_2)_tors = tors_invs(F_invs[k])
      - Fs_invs[k] (k = 1..H): invariant factors of F^*_{H-k}(L_1^v, L_2^v)
      - Q_invs[h]  (h = 0..H): invariant factors of Fil^h_Hod(L_1, L_2) -> Q_h = C_h(L_2, L_1)_tors = tors_invs(Q_invs[h])
      - Qs_invs[h] (h = 0..H): invariant factors of Fil^*_h
      - F_gens[k], Q_gens[h]: explicit generating vectors of F_{-k} in Z^d and Fil^h in Z^d (for exact length identity checks!)
    """
    d = P.rows
    inv = sp.simplify(P.inv())
    H = 0
    for i in range(d):
        for j in range(d):
            _, den = sp.fraction(sp.together(inv[i, j]))
            den_p = sp.Poly(sp.expand(den), E_sym)
            if len(den_p.terms()) != 1:
                return None
            (k,), c = den_p.terms()[0]
            if int(c) % p == 0:
                return None
            if k > H:
                H = k
    if H == 0:
        return None
    Ps = sp.simplify(E_sym**H * inv).T

    def compute_one(Mat):
        coeffs = {k: [[0] * d for _ in range(d)] for k in range(H + 2)}
        for i in range(d):
            for j in range(d):
                for (k,), c in sp.Poly(sp.expand(Mat[i, j]), E_sym).terms():
                    if k <= H + 1:
                        coeffs[k][i][j] = int(c)

        def toeplitz(N):
            T = [[0] * (d * N) for _ in range(d * N)]
            for j in range(N):
                for i in range(j, N):
                    C = coeffs.get(i - j)
                    if C:
                        for a in range(d):
                            for b in range(d):
                                T[i * d + a][j * d + b] = C[a][b]
            return T

        # F_{-k} = im(L_2 cap E^k L_1 -> L_2 / E L_2) = {v_0 : P v = 0 mod E^k} for k = 0..H+1
        # Wait: for k = 0: F_0 = all of L_2/EL_2 (rank d, zero torsion)
        # For k = 1..H: F_{-k} = {v_0 : P v = 0 mod E^k}
        # For k = H+1: E^{H+1} L_1 <= E L_2, so F_{-(H+1)} = 0!
        F_gens = {}
        F_invs = {}
        X_invs = {}
        F_gens[0] = [[1 if i == j else 0 for j in range(d)] for i in range(d)]
        F_invs[0] = [0] * d
        for k in range(1, H + 1):
            T = toeplitz(k)
            X_invs[k] = tors_invs(snf_p_invariants(T, p))
            kb = p_sat_ker(T, p)
            if not kb:
                F_gens[k] = []
                F_invs[k] = []
            else:
                # Each v in kb gives a vector v[:d] in Z^d
                vecs = [v[:d] for v in kb]
                F_gens[k] = vecs
                mat = [[v[a] for v in vecs] for a in range(d)]
                F_invs[k] = snf_p_invariants(mat, p)
        F_gens[H + 1] = []
        F_invs[H + 1] = []

        # Fil^{-h}_Hod(L_1, L_2) = im(L_1 cap E^{-h} L_2 -> L_1 / E L_1) for h = 0..H
        # Note: for L_2 <= L_1, E^{-h} L_2 INCREASES with h!
        # Wait: h=0 is im(L_2 -> L_1/EL_1) = P(0) Z^d.
        # h=H is all of L_1/EL_1 (since E^H L_1 <= L_2 => L_1 <= E^{-H} L_2!).
        # h=-1 is 0 (since E L_2 <= E L_1 => im = 0!).
        Q_gens = {}
        Q_invs = {}
        Q_gens[-1] = []
        Q_invs[-1] = []
        for h_loc in range(0, H + 1):
            Tf = toeplitz(h_loc + 1)
            At, Bb = Tf[: d * h_loc], Tf[d * h_loc :]
            if h_loc == 0:
                # cols of Bb are P(0) columns
                vecs = [[Bb[a][c] for a in range(d)] for c in range(d)]
                Q_gens[0] = vecs
                Q_invs[0] = snf_p_invariants(Bb, p)
            else:
                kb = p_sat_ker(At, p)
                if not kb:
                    Q_gens[h_loc] = []
                    Q_invs[h_loc] = []
                else:
                    vecs = [[sum(Bb[a][c] * v[c] for c in range(len(v))) for a in range(d)] for v in kb]
                    Q_gens[h_loc] = vecs
                    mat = [[v[a] for v in vecs] for a in range(d)]
                    Q_invs[h_loc] = snf_p_invariants(mat, p)
        return F_gens, F_invs, Q_gens, Q_invs, X_invs

    Fg, Fi, Qg, Qi, Xi = compute_one(P)
    Fsg, Fsi, Qsg, Qsi, Xsi = compute_one(Ps)
    return H, Ps, Fg, Fi, Qg, Qi, Xi, Fsg, Fsi, Qsg, Qsi, Xsi


# =============================================================================
# SUITE 1: Theorem L01-1 — Exact Disproof of d-Independent K02-Q1 via P_{n,k}
# =============================================================================

def run_suite_1():
    print("=== SUITE 1: Theorem L01-1 (Staircase Counterexample Family P_{n,k}, Sharp c_opt(d) = floor(d/2)) ===")

    # 1.1 Explicit minimal d=4 counterexample P_{2,1} refuting c=1 at d=4, H=4 (for p=2, 3, 5)
    for pr in [2, 3, 5]:
        P2 = build_Pn(2, p=pr, k=1)
        H, _, _, Fi, _, Qi, Xi, _, Fsi, _, Qsi, _ = compute_exact_data(P2, p=pr)
        assert H == 4
        Phi = max(exp_from_invs(Fi[k]) for k in range(1, H + 1))
        Phis = max(exp_from_invs(Fsi[k]) for k in range(1, H + 1))
        Q1_invs = tors_invs(Qi[1])  # h_loc = 1 corresponds to M_2 = E^{-1} P_2 S^4 (M=3, h=1)
        assert Phi == 1 and Phis == 1, f"Expected Phi=Phi^*=1 for P_{{2,1}} (p={pr}), got {Phi}, {Phis}"
        assert Q1_invs == [2], f"Expected Q_1_tors = O/p^2 ([2]) for P_{{2,1}} (p={pr}), got {Q1_invs}"
        assert [Xi[m] for m in range(1, H + 1)] == [[1], [2], [1], []]
    print("  [PASS] 1.1 Minimal d=4, H=4 counterexample P_{2,1} verified for p=2,3,5: Phi=Phi^*=1, Q_1_tors = O/p^2 (refutes c=1!).")

    # 1.2 Infinite family P_{n,k} for n=2,3,4,5 (k=1) and n=2,3 (k=2), plus odd-rank d=2n+1
    for n, k, pr in [(2, 1, 2), (3, 1, 2), (4, 1, 2), (5, 1, 2), (2, 2, 2), (3, 2, 2), (3, 1, 3)]:
        P = build_Pn(n, p=pr, k=k)
        H, _, _, Fi, _, Qi, Xi, _, Fsi, _, Qsi, _ = compute_exact_data(P, p=pr)
        assert H == 2 * n
        Phi = max(exp_from_invs(Fi[m]) for m in range(1, H + 1))
        Phis = max(exp_from_invs(Fsi[m]) for m in range(1, H + 1))
        Q_peak_invs = tors_invs(Qi[n - 1])
        expected_X = [[min(m, 2 * n - m) * k] if m < 2 * n else [] for m in range(1, 2 * n + 1)]
        assert Phi == k and Phis == k, f"P_{{{n},{k}}}: expected Phi=Phi^*={k}, got {Phi}, {Phis}"
        assert Q_peak_invs == [n * k], f"P_{{{n},{k}}}: expected Q_1_tors=[{n*k}], got {Q_peak_invs}"
        assert [Xi[m] for m in range(1, H + 1)] == expected_X, f"X_m mismatch on P_{{{n},{k}}}"
        print(f"    P_{{{n},{k}}} (p={pr}, d={2*n:2d}, H={H:2d}): Phi={Phi}, Phi^*={Phis}, Q_1_tors=O/p^{n*k} -> ratio={n} == floor(d/2)")

    # 1.3 Odd rank d=2n+1 witness P_{n,1} (+) [1] achieves floor(d/2) = n
    for n in [2, 3]:
        P_odd = sp.diag(build_Pn(n, p=2, k=1), sp.Matrix([[1]]))
        H, _, _, Fi, _, Qi, _, _, Fsi, _, _, _ = compute_exact_data(P_odd, p=2)
        Phi = max(exp_from_invs(Fi[m]) for m in range(1, H + 1))
        Phis = max(exp_from_invs(Fsi[m]) for m in range(1, H + 1))
        Q_peak = exp_from_invs(Qi[n - 1])
        assert Phi == 1 and Phis == 1 and Q_peak == n == (2 * n + 1) // 2
    print("  [PASS] 1.2-1.3 Staircase family P_{n,k} (d=4,6,8,10) & odd-rank d=5,7 match closed-form proof exactly.")


# =============================================================================
# SUITE 2: Theorem L01-2 — Exact Length Identities (*_-), (*_+) & Sharp Bound
# =============================================================================

def verify_exact_length_identities(P: sp.Matrix, p: int = 2):
    """
    Verify BOTH exact length identities (*_-) and (*_+) for EVERY shift h_loc in 0..H,
    AND verify:
      exp(Q_1) <= len(Q_1) <= min(d^- * Phi, d^+ * Phi^*) <= floor(d/2) * max(Phi, Phi^*).
    """
    d = P.rows
    res = compute_exact_data(P, p=p)
    if res is None:
        return None
    H, Ps, Fg, Fi, Qg, Qi, Xi, Fsg, Fsi, Qsg, Qsi, Xsi = res

    # For L_1 = S^d, L_2 = P S^d, E^H L_1 <= L_2 <= L_1:
    # Shift by h_loc in 0..H: M_1 = L_1, M_2 = E^{-h_loc} L_2 (so E^{H-h_loc} M_1 <= M_2 <= E^{-h_loc} M_1,
    # M = H - h_loc, h = h_loc).
    # Dictionary between (M_1, M_2) index i and (L_1, L_2) index:
    #   F_i(M_1, M_2) = F_{i - h_loc}(L_1, L_2) = Fg[h_loc - i]  (for i in [-(H-h_loc), h_loc])
    #   T_i(M_1, M_2) = C_i(M_1, M_2)_tors -> len(T_i) = len_from_invs(Fi[h_loc - i])
    #   Fil^i_Hod(M_1, M_2) = Fil^{i - h_loc}_Hod(L_1, L_2) = Qg[h_loc - i]
    #   Q_i(M_1, M_2) -> len(Q_i) = len_from_invs(Qi[h_loc - i])
    # Dual (M_1^v, M_2^v): M_1^v = L_1^v, M_2^v = E^{h_loc} L_2^v = E^{h_loc - H} L_2^* (L_2^* = Ps S^d):
    #   F^*_j(M_1^v, M_2^v) = F_{j + h_loc - H}(L_1^*, L_2^*) = Fsg[H - h_loc - j]
    #   T^*_j(M_1^v, M_2^v) -> len(T^*_j) = len_from_invs(Fsi[H - h_loc - j])
    #   Fil^*_j(M_1^v, M_2^v) = Qsg[H - h_loc - j]
    #   Q^*_j(M_1^v, M_2^v) -> len(Q^*_j) = len_from_invs(Qsi[H - h_loc - j])

    # Precompute W_k/A_k = coker(T_{-k-1} -> T_{-k}) and V_k/A_k = coker(Q_{-k+1} -> Q_{-k})
    # in terms of L_1, L_2 index k = h_loc - i (so k runs from 0 to H; as i increases by 1, k decreases by 1!)
    # Check:
    #   F_{i-1} <= F_i corresponds to Fg[k+1] <= Fg[k]!
    #   S_i = sat(Fg[k]), S_{i-1} = sat(Fg[k+1]).
    #   coker(T_{i-1} -> T_i) = S_i / (S_{i-1} + F_i) = sat(Fg[k]) / (sat(Fg[k+1]) + Fg[k])!
    #   Fil^{i+1} <= Fil^i corresponds to Qg[k-1] <= Qg[k]!
    #   U_i = sat(Qg[k]), U_{i+1} = sat(Qg[k-1]).
    #   coker(Q_{i+1} -> Q_i) = U_i / (U_{i+1} + Fil^i) = sat(Qg[k]) / (sat(Qg[k-1]) + Qg[k])!
    def compute_cokers(G_dict, idx_lo, idx_hi, step_prev):
        # For each k in [idx_lo, idx_hi], compute len(sat(G[k]) / (sat(G[k + step_prev]) + G[k]))
        sats = {k: p_sat_span(G_dict.get(k, []), p) for k in range(idx_lo - 1, idx_hi + 2)}
        lens = {}
        ranks = {}
        for k in range(idx_lo, idx_hi + 1):
            Sk = sats[k]
            Sprev = sats[k + step_prev]
            ranks[k] = len(Sk) - len(Sprev)
            if not Sk:
                lens[k] = 0
            else:
                sub = Sprev + G_dict.get(k, [])
                invs = sublattice_quotient_invs(sub, Sk, p)
                lens[k] = len_from_invs(invs)
        return lens, ranks

    len_W_over_A, rk_F = compute_cokers(Fg, 0, H, +1)       # k = h_loc - i: Fg[k+1] <= Fg[k]
    len_V_over_A, rk_Q = compute_cokers(Qg, 0, H, -1)       # k = h_loc - i: Qg[k-1] <= Qg[k]
    len_Ws_over_B, rk_Fs = compute_cokers(Fsg, 0, H, +1)    # ks = H - h_loc - j = H - k (at j = -i)
    len_Vs_over_B, rk_Qs = compute_cokers(Qsg, 0, H, -1)

    # Verify rank match and Gram length identity at EVERY k in 0..H!
    # At index i (so k = h_loc - i), -i corresponds to ks = H - h_loc - (-i) = H - k!
    for k in range(0, H + 1):
        ks = H - k
        assert rk_F[k] == rk_Q[k] == rk_Fs[ks] == rk_Qs[ks], (
            f"Weight multiplicity mismatch at k={k}: {rk_F[k]}, {rk_Q[k]}, {rk_Fs[ks]}, {rk_Qs[ks]}"
        )
        # Gram identity: len(V/A) + len(V^v/B) == len(W/A) + len(W^v/B)!
        assert len_V_over_A[k] + len_Vs_over_B[ks] == len_W_over_A[k] + len_Ws_over_B[ks], (
            f"Gram length identity failed at k={k}!"
        )

    Phi = max(exp_from_invs(Fi[m]) for m in range(1, H + 1))
    Phis = max(exp_from_invs(Fsi[m]) for m in range(1, H + 1))

    # Now check BOTH exact length identities (*_-) and (*_+) for EVERY shift h_loc in 0..H!
    for h_loc in range(0, H + 1):
        M = H - h_loc
        h = h_loc
        len_Q0 = len_from_invs(Qi[h_loc])
        exp_Q0 = exp_from_invs(Qi[h_loc])
        len_Tm1 = len_from_invs(Fi[h_loc + 1])  # i = -1 => k = h_loc - (-1) = h_loc + 1

        # Identity (*_-): i in [-M, -1] <=> k = h_loc - i in [h_loc + 1, H]
        rhs_minus = sum(len_W_over_A[k] - len_V_over_A[k] for k in range(h_loc + 1, H + 1)) - len_Tm1
        assert len_Q0 == rhs_minus, f"(*_-) failed at h_loc={h_loc}: {len_Q0} != {rhs_minus}"

        # Identity (*_+): i in [0, h] <=> k = h_loc - i in [0, h_loc] <=> ks = H - k in [H - h_loc, H]
        rhs_plus = sum(len_Ws_over_B[H - k] - len_Vs_over_B[H - k] for k in range(0, h_loc + 1)) - len_Tm1
        assert len_Q0 == rhs_plus, f"(*_+) failed at h_loc={h_loc}: {len_Q0} != {rhs_plus}"

        # Check refined multiplicity-weighted bounds and min(d^- Phi, d^+ Phi^*) <= floor(d/2) max(Phi, Phi^*)
        d_minus = sum(rk_F[k] for k in range(h_loc + 1, H + 1))
        d_plus = sum(rk_F[k] for k in range(0, h_loc + 1))
        assert d_minus + d_plus == d
        b_minus = sum(rk_F[k] * exp_from_invs(Fi[k]) for k in range(h_loc + 1, H + 1)) - len_Tm1
        b_plus = sum(rk_F[k] * exp_from_invs(Fsi[H - k]) for k in range(0, h_loc + 1)) - len_Tm1
        assert len_Q0 <= b_minus and len_Q0 <= b_plus
        assert exp_Q0 <= len_Q0 <= min(d_minus * Phi, d_plus * Phis) <= (d // 2) * max(Phi, Phis)

        # Also check distinct nonnegative-weight bound (Theorem L01-4):
        # distinct nonnegative weights are {i in [0, h] : rk_F[h_loc - i] > 0}
        pos_ks = [k for k in range(0, h_loc + 1) if rk_F[k] > 0]
        r_plus = len(pos_ks)
        if r_plus == 0:
            assert exp_Q0 == 0
        else:
            # Recall k = 0 corresponds to i = h_loc = h (largest weight b_{r^+}), where Fi[0] = 0!
            # Wait: largest nonnegative weight b_{r^+} has smallest k = min(pos_ks)!
            k_top = min(pos_ks)
            # Wait: at k_top, is T_{b_{r^+}} = 0? Check: F_{b_{r^+}} = F_h = M_2/EM_2, YES because NO weights > b_{r^+}!
            assert exp_from_invs(Fi[k_top]) == 0 or all(rk_F[kk] == 0 for kk in range(0, k_top))
            # Check exact sum bound: sum_{k in pos_ks \ {k_top}} exp(T_i) + sum_{k in pos_ks} exp(T^*_{-i})
            b_rplus = sum(exp_from_invs(Fi[k]) for k in pos_ks if k != k_top) + sum(
                exp_from_invs(Fsi[H - k]) for k in pos_ks
            )
            assert exp_Q0 <= b_rplus <= (r_plus - 1) * Phi + r_plus * Phis, (
                f"r^+ bound failed at h_loc={h_loc}: exp_Q0={exp_Q0} > {b_rplus}"
            )
            if r_plus == 1:
                assert exp_Q0 <= exp_from_invs(Fsi[H - k_top]) <= Phis

        # Also check sharp width bound (Theorem L01-3 Corollary):
        # exp(Q_1) <= min((M - 1)_+ * Phi, (h + 1) * Phis) <= floor(H / 2) * max(Phi, Phis)
        assert exp_Q0 <= max(0, M - 1) * Phi
        assert exp_Q0 <= (h + 1) * Phis
        assert exp_Q0 <= (H // 2) * max(Phi, Phis)
    return True


def run_suite_2():
    print("=== SUITE 2: Theorem L01-2 (Exact Length Identities (*_-), (*_+), Sharp Rank-d Bound & Unconditional d=3 c=1) ===")
    p = 2
    E = E_sym
    named = [
        ("P_a", sp.Matrix([[E**4, p * E**2 + p**2 * E, p**3], [0, E**2, p * E + p**2], [0, 0, E**2]])),
        ("t37", sp.Matrix([[E, 0, 2], [0, E**2, 4 + 2 * E], [0, 0, E**2]])),
        ("P_kill4", sp.Matrix([[E, 0, 2, 0], [0, E**2, 16, 2 * E**2], [0, 0, E**2, 0], [0, 0, 0, E**3]])),
        ("P_sq2", sp.Matrix([[E, 0, 4, 0], [0, E**2, 16, 4 * E], [0, 0, E**2, 4], [0, 0, 0, E**3]])),
        ("P_sq3", sp.Matrix([[E, 0, 4, 0], [0, E**2, 16, 4 * E], [0, 0, E**2, 2], [0, 0, 0, E**3]])),
        ("P_tw5", sp.Matrix([[E**2, p, 0, 0], [0, E, 1, 0], [0, 0, E**2, p], [0, 0, 0, E]])),
        ("P5_v0", sp.Matrix([[E, 0, 2, 2, E], [0, E**2, 4, 2 * E, 0], [0, 0, E**2, 0, 0], [0, 0, 0, E**2, 0], [0, 0, 0, 0, E**2]])),
        ("P_{2,1}", build_Pn(2, p=2, k=1)),
        ("P_{3,1}", build_Pn(3, p=2, k=1)),
        ("P_{2,2}", build_Pn(2, p=2, k=2)),
    ]
    for name, P in named:
        assert verify_exact_length_identities(P, p=2)
    print(f"  [PASS] 2.1 Exact length identities (*_-), (*_+), Gram identity, r^+ bound, and width bound verified on {len(named)} named matrices.")

    # Non-triangular 3x3 matrices (built via U * T * V with unimodular U, V in GL_3(Z[E]))
    random.seed(20261123)
    checked_3x3_nontri = 0
    for _ in range(40):
        ex = [random.choice([0, 1, 2, 3]) for _ in range(3)]
        T = sp.eye(3)
        for i in range(3):
            T[i, i] = E ** ex[i]
        for i in range(3):
            for j in range(i + 1, 3):
                T[i, j] = sum(random.choice([0, 1, 2, 4]) * E**k for k in range(2))
        # Apply lower-triangular unimodular U, V to make genuinely non-triangular!
        U = sp.eye(3)
        V = sp.eye(3)
        U[1, 0] = random.choice([0, 1, E, 2])
        U[2, 0] = random.choice([0, 1, E])
        U[2, 1] = random.choice([0, 1, 2])
        V[1, 0] = random.choice([0, 1, E])
        V[2, 1] = random.choice([0, 1, E, 2])
        P = sp.expand(U * T * V)
        if verify_exact_length_identities(P, p=2):
            checked_3x3_nontri += 1

    # Random 4x4 & 5x5 matrices over p=2 and p=3
    checked_rand = 0
    for pr in [2, 3]:
        for t in range(40):
            d = 4 if t < 30 else 5
            ex = [random.choice([0, 1, 2]) for _ in range(d)]
            P = sp.eye(d)
            for i in range(d):
                P[i, i] = E ** ex[i]
            for i in range(d):
                for j in range(i + 1, d):
                    P[i, j] = sum(random.choice([0, 0, 1, pr, pr**2]) * E**k for k in range(2))
            if verify_exact_length_identities(P, p=pr):
                checked_rand += 1
    print(f"  [PASS] 2.2 Verified (*_-), (*_+), and Theorem L01-2/L01-4 on {checked_3x3_nontri} non-triangular 3x3 (c=1!) + {checked_rand} random 4x4/5x5 matrices.")


# =============================================================================
# SUITE 3: Theorem L01-4 — Asymmetry Between r^+=1 (c=1 holds) and r^-=1 (fails)
# =============================================================================

def run_suite_3():
    print("=== SUITE 3: Theorem L01-4 (r^+=1 Exact Quotient Bound vs r^-=1 Counterexample) ===")

    # Construct explicit two-weight {0, 0, 4, 4} lattice pair from T3^T:
    # Z(E) = [[1/2, 0], [0, 0]] + [[0, 1/4], [1/2, 0]] * E (the transpose of T3!)
    # M_2 = {(a, b) in S^4 : a = Z(E) b mod E^4}
    # Let us construct an explicit 4x4 basis matrix P over Z[E] for this exact lattice M_2!
    # Check: a_1 = (1/2) b_1 + (1/4) E b_2 (mod E^4), a_2 = (1/2) E b_1 (mod E^4)
    # Wait:
    #   b_1 = 2, b_2 = 0 => a_1 = 1, a_2 = E => col v1 = [1, E, 2, 0]^T
    #   b_1 = 0, b_2 = 4 => a_1 = E, a_2 = 0 => col v2 = [E, 0, 0, 4]^T
    #   Wait: is (a, b) = (0, 0, 0, 2 E^3) in M_2? Yes! 1/4 E * (2 E^3) = 1/2 E^4 = 0 mod E^4!
    #   Better: solve directly using (b_1, b_2):
    #   v1 = [1, E, 2, 0]^T
    #   v2 = [E, 0, 0, 4]^T - wait: take b_2 = 2 E^3 => [0, 0, 0, 2 E^3]^T? No, E^3 * v2 / 2 = [E^4/2, 0, 0, 2 E^3]
    #   Let us build a clean explicit Z_2[E]-basis of M_2:
    #   b = (2, 0) -> v1 = [1, E, 2, 0]
    #   b = (0, 4) -> v2 = [E, 0, 0, 4]  -- wait, also b = (0, 2 E^3) -> [E^4/2, ...] -> a_1 = 0 mod E^4 => [0, 0, 0, 2 E^3] + [E^4, 0, 0, 0]?
    #   Actually: (1/4) E * (2 E^3) = (1/2) E^4 = 0 in Q[E]/E^4! So [0, 0, 0, 2 E^3] IS in M_2!
    #   Wait: v2 - 2*[0,0,0,2E^3] still has 4 in row 3. What is the free S-basis of M_2?
    #   Let us check: e_1*E^4, e_2*E^4, v1=[1, E, 2, 0], v3=[0, 0, 0, 2 E^3]?
    #   Check det of [v1, v2, [E^4, 0, 0, 0], [0, E^4, 0, 0]]: det = 8 E^8 (NOT p-saturated!).
    #   Factor out the 2-power:
    #   - [0, E^4, 0, 0]: check 2*[0, E^4, ...] vs E^3 * v1 = [E^3, E^4, 2 E^3, 0]
    #   - Wait: b = (2 E^2, -4 E) -> a_1 = E^2 - E^2 = 0, a_2 = E^3 -> divisible by 2? No, a_2 = E^3!
    #   Let us just find the 4 free generators of M_2 explicitly:
    #   Notice: a_1 = (b_1 + E b_2 / 2)/2, a_2 = E b_1 / 2 (mod E^4)!
    #   So b_1 = 2 u_1 (u_1 in S), giving a_2 = E u_1, and a_1 = u_1 + E b_2 / 4!
    #   Wait: if b_1 = 2 u_1 + c_3 E^3 (so E b_1 / 2 = E u_1 + c_3 E^4 / 2 == E u_1 mod E^4!!):
    #   Aha! Take b_1 = E^3, b_2 = 2 E^2 => a_1 = E^3/2 + E^3/2 = E^3, a_2 = 0 mod E^4 => w1 = [E^3, 0, E^3, 2 E^2]!
    #   Take b_1 = 2, b_2 = 0 => w2 = [1, E, 2, 0]!
    #   Take b_1 = 0, b_2 = 4 => w3 = [E, 0, 0, 4]!
    #   Wait: E^2 * w3 - 2 * w1 = [E^3 - 2 E^3, 0, -2 E^3, 4 E^2 - 4 E^2] = [-E^3, 0, -2 E^3, 0]
    #   And E^3 * w2 = [E^3, E^4, 2 E^3, 0] => sum = [0, E^4, 0, 0]!
    #   Still det([w2, w3, w1, [E^4, 0, 0, 0]]) = det([[1,E,E^3,E^4],[E,0,0,0],[2,0,E^3,0],[0,4,2E^2,0]])
    #   = -E^4 * (-E) * (2*2*E^2 - 4*E^3) ... wait, let us check!
    #   Instead, construct directly with w1=[1, E, 2, 0], w2=[E, 0, 0, 4], w3=[E^3, 0, E^3, 2E^2], w4=[0, 0, 0, 2E^3]:
    #   Wait: check det of [[1, E, E^3, 0], [E, 0, 0, 0], [2, 0, E^3, 0], [0, 4, 2E^2, 2E^3]] = -E * (E * E^3 * 2E^3) = ... no, factor of 2!
    #   Wait: b_1 = E^3, b_2 = 2 E^2 gives [E^3, 0, E^3, 2 E^2]. Also b_1 = 0, b_2 = 2 E^3 gives [0, 0, 0, 2 E^3]!
    #   What about b_1 = E^3, b_2 = 0? a_1 = E^3/2 (not integral).
    #   What about b_1 = 2 E, b_2 = -4? a_1 = E - E = 0, a_2 = E^2 => [0, E^2, 2 E, -4]!
    #   Aha! Express directly in u = a_1, v = b_2:
    #     b_1 = 2 a_1 - E b_2 / 2 (mod E^4)!
    #     So E b_2 must be even! Write b_2 = 2 t_2 + c E^3!
    #     Then b_1 = 2 a_1 - E t_2 - c E^4/2 == 2 a_1 - E t_2 (mod E^4)!
    #     And a_2 = E b_1 / 2 = E a_1 - E^2 t_2 / 2 (mod E^4)!
    #     So E^2 t_2 must be even! Write t_2 = 2 s_2 + d E^2!
    #     Then b_2 = 4 s_2 + 2 d E^2 + c E^3!
    #     b_1 = 2 a_1 - 2 E s_2 - d E^3!
    #     a_2 = E a_1 - E^2 s_2 - d E^4/2 == E a_1 - E^2 s_2 (mod E^4)!
    #   OMG!! LOOK HOW CLEAN THAT FREE S-BASIS OF M_2 IS!!
    #   Independent free S-parameters: a_1, s_2, plus E^4 a_2_free, plus ... wait:
    #     Param a_1:  [1,   E,    2,   0  ]^T
    #     Param s_2:  [0,  -E^2, -2E,  4  ]^T
    #     Param d:    [0,   0,   -E^3, 2E^2]^T  (check: a_1=0, a_2=0, b_1=-E^3, b_2=2E^2 => Z b = (-E^3/2 + E^3/2, -E^4/2) = (0, 0) mod E^4!)
    #     Param c:    [0,   0,    0,   E^3]^T? Wait: b_2 = E^3 => Z_1 b_2 E = (1/4) E^4 = 0 mod E^4!!
    #     YES!! b_2 = E^3 gives (a_1, a_2) = (0, 0) mod E^4!!
    #   CHECK DETERMINANT OF THOSE 4 COLUMNS!!
    #     col0 = [1,  E,   2,   0  ]
    #     col1 = [0, -E^2, -2E, 4  ]
    #     col2 = [0,  0,  -E^3, 2E^2] -> WAIT: E*col2 = [0,0,-E^4, 2E^3], and [0,0,0,E^3] is col3!
    #     Wait: det([col0, col1, col2, col3]) = 1 * (-E^2) * (-E^3) * E^3 = +E^8!! UNIT DETERMINANT * E^8!!
    E = E_sym
    P_tw = sp.Matrix([
        [1,  0,     0,      0],
        [E, -E**2,  0,      0],
        [2, -2*E,  -E**3,   0],
        [0,  4,     2*E**2, E**3],
    ])
    assert sp.expand(P_tw.det()) == E**8
    H, Ps, Fg, Fi, Qg, Qi, Xi, Fsg, Fsi, Qsg, Qsi, Xsi = compute_exact_data(P_tw, p=2)
    assert H == 4
    # Verify exact weights are {0, 0, 4, 4} (r^- = 1, r^+ = 1) via verify_exact_length_identities!
    assert verify_exact_length_identities(P_tw, p=2)
    Phi = max(exp_from_invs(Fi[m]) for m in range(1, H + 1))
    Phis = max(exp_from_invs(Fsi[m]) for m in range(1, H + 1))
    Qe = [exp_from_invs(Qi[h]) for h in range(H + 1)]
    # Check weights explicitly: rk_F[k] nonzero only at k=0 and k=4!
    # Wait: Fi[0] has rank 4, Fi[1..4] have rank 2, Fi[5] has rank 0 => jumps ONLY at k=0 and k=4!
    ranks_F = [len(Fi[k]) for k in range(H + 2)]
    assert ranks_F == [4, 2, 2, 2, 2, 0], f"Expected two-weight ranks [4,2,2,2,2,0], got {ranks_F}"
    assert Phi == 1 and Phis == 2 and Qe[0] == 2 and Qe[1] == 2, (
        f"Unexpected T3^T invariants: Phi={Phi}, Phis={Phis}, Qe={Qe}"
    )
    print(f"  [PASS] 3.1 Explicit 4x4 two-weight {{0,0,4,4}} matrix P_tw (r^-=r^+=1, d^-=d^+=2): Phi={Phi}, Phi^*={Phis}, Qe={Qe}.")
    print("             At h_loc=1 (M=3, h=1): exp(Q_1) = 2 > 1 = r^- * Phi (r^- cannot replace d^-!), while exp(Q_1) = 2 <= 2 = Phi^* (r^+=1 holds!).")


# =============================================================================
# SUITE 4: Theorem L01-3 — Exact Matlis Duality Four-Fold Dictionary
# =============================================================================

def verify_matlis_fourfold(P: sp.Matrix, p: int = 2):
    """
    Directly construct X_m = (P S^d + E^m S^d)^sat / (P S^d + E^m S^d) and the maps
      alpha_m : X_{m-1} --(*E)--> X_m   and   beta_m : X_m --(proj)--> X_{m-1}
    and assert EXACT INVARIANT-FACTOR EQUALITY with:
      ker(*E)   == C_{-m}(L_1, L_2)_tors
      coker(*E) == C_{m-1}(L_1^v, L_2^v)_tors
      ker(proj) == C_{m-1}(L_2, L_1)_tors
      coker(proj) == C_{-m}(L_2^v, L_1^v)_tors.
    """
    d = P.rows
    res = compute_exact_data(P, p=p)
    assert res is not None
    H, Ps, Fg, Fi, Qg, Qi, Xi, Fsg, Fsi, Qsg, Qsi, Xsi = res

    coeffs = {k: [[0] * d for _ in range(d)] for k in range(H + 2)}
    for i in range(d):
        for j in range(d):
            for (k,), c in sp.Poly(sp.expand(P[i, j]), E_sym).terms():
                if k <= H + 1:
                    coeffs[k][i][j] = int(c)

    def toeplitz(N):
        T = [[0] * (d * N) for _ in range(d * N)]
        for j in range(N):
            for i in range(j, N):
                C = coeffs.get(i - j)
                if C:
                    for a in range(d):
                        for b in range(d):
                            T[i * d + a][j * d + b] = C[a][b]
        return T

    # For each m = 1..H:
    #   N_m / E^m S^d = col-span of T_m in Z^{d*m}
    #   N_m^sat / E^m S^d = p-saturation S_m of col-span of T_m in Z^{d*m}
    #   X_m = S_m / im(T_m)
    S_bases = {0: []}
    T_cols = {0: []}
    for m in range(1, H + 1):
        Tm = toeplitz(m)
        cols = [[Tm[r][c] for r in range(d * m)] for c in range(d * m)]
        T_cols[m] = cols
        S_bases[m] = p_sat_span(cols, p)

    # Express im(T_m) in basis S_m -> matrix M_m (rank r_m x (d*m))
    # Express (*E)(S_{m-1}) in basis S_m -> matrix E_m (rank r_m x r_{m-1})
    # Express (proj)(S_m) in basis S_{m-1} -> matrix R_m (rank r_{m-1} x r_m)
    def express_in(basis, vecs):
        if not basis:
            return []
        if not vecs:
            return [[] for _ in basis]
        B_sp = sp.Matrix(basis).T
        T_sp = sp.Matrix(vecs).T
        piv = list(B_sp.T.rref()[1])
        X = B_sp[piv, :].inv() * T_sp[piv, :]
        den = sp.lcm([sp.fraction(sp.together(X[i, j]))[1] for i in range(X.rows) for j in range(X.cols)])
        assert int(den) % p != 0
        # Multiply by inverse of den mod p^45? Better: keep rational exact or clear den by multiplying by unit!
        # Since den is coprime to p, scaling all columns by den does NOT change the Z_(p)-module!
        return [[int(X[i, j] * den) for j in range(X.cols)] for i in range(X.rows)], int(den)

    # Actually, to compose matrices consistently, clear denominators per-column or keep exact rational matrices via sympy!
    def express_exact(basis, vecs):
        if not basis:
            return sp.zeros(0, len(vecs))
        if not vecs:
            return sp.zeros(len(basis), 0)
        B_sp = sp.Matrix(basis).T
        T_sp = sp.Matrix(vecs).T
        piv = list(B_sp.T.rref()[1])
        return B_sp[piv, :].inv() * T_sp[piv, :]

    def mat_to_int_scaled(M_sp):
        if M_sp.rows == 0 or M_sp.cols == 0:
            return [], 1
        den = sp.lcm([sp.fraction(sp.together(M_sp[i, j]))[1] for i in range(M_sp.rows) for j in range(M_sp.cols)])
        assert int(den) % p != 0
        return [[int(M_sp[i, j] * den) for j in range(M_sp.cols)] for i in range(M_sp.rows)], int(den)

    def ker_coker_invs(A_sp, M_dom_sp, M_cod_sp):
        """
        Compute exact torsion invariant factors of ker and coker of
          f : (Z_p^{r1} / im(M_dom)) --(A)--> (Z_p^{r2} / im(M_cod))
        assuming both domain and codomain are finite p-groups (M_dom, M_cod full row rank).
        """
        r1 = M_dom_sp.rows
        r2 = M_cod_sp.rows
        # Coker: Z_p^{r2} / (im(A) + im(M_cod))
        if r2 == 0:
            coker_inv = []
        else:
            comb = sp.Matrix.hstack(A_sp, M_cod_sp) if A_sp.cols > 0 else M_cod_sp
            comb_int, _ = mat_to_int_scaled(comb)
            coker_inv = tors_invs(snf_p_invariants(comb_int, p))

        # Ker: K / im(M_dom) where K = { x in Z_p^{r1} : A x in im(M_cod) }
        # Wait: by exact sequence 0 -> im(M_dom) -> K -> ker(f) -> 0:
        # Compute Z_(p)-basis of K!
        if r1 == 0:
            ker_inv = []
        elif r2 == 0:
            # A = 0, so K = Z_p^{r1}, ker(f) = Z_p^{r1} / im(M_dom)
            dom_int, _ = mat_to_int_scaled(M_dom_sp)
            ker_inv = tors_invs(snf_p_invariants(dom_int, p))
        else:
            # Solve [A, -M_cod] [x; y] = 0 over Z_(p), extract x-part -> spans K!
            # Clear common p'-denominator of [A, -M_cod]
            aug = sp.Matrix.hstack(A_sp, -M_cod_sp)
            aug_int, _ = mat_to_int_scaled(aug)
            kvecs = p_sat_ker(aug_int, p)
            # Wait: x-projections of kvecs generate K (over Z_(p))!
            # Because any x in K has A x = M_cod y for some y in Z_(p)^{cols}, so (x, y) is in ker_{Z_(p)}([A, -M_cod])!
            x_cols = [v[:r1] for v in kvecs]  # list of vectors in Z^{r1} generating K over Z_(p)!
            # Now we need invariant factors of K / im(M_dom)!
            # Since K has full rank r1 inside Z_p^{r1}, compute a Z_(p)-basis of K via HNF/SNF?
            # Even simpler: let K_mat be r1 x s matrix of x_cols, compute SNF of K_mat over Z_(p):
            # Actually, using exact rational left-action: let U * K_mat * V = D, NO — even simpler!
            # Since M_dom has full row rank r1, pick a basis of K by finding a Z_(p)-basis of the column space of x_cols:
            # Standard p-adic Hermite/row reduction on x_cols^T (rows = x_cols) gives an r1 x r1 basis matrix B_K of K!
            # Let us do exact p-adic column-basis reduction on x_cols!
            K_basis = p_adic_col_basis(x_cols, r1, p)
            B_K_sp = sp.Matrix(K_basis).T  # r1 x r1
            # Express M_dom in basis B_K: Q = B_K^{-1} * M_dom
            Q_sp = B_K_sp.inv() * M_dom_sp
            Q_int, _ = mat_to_int_scaled(Q_sp)
            ker_inv = tors_invs(snf_p_invariants(Q_int, p))
        return ker_inv, coker_inv

    def p_adic_col_basis(vecs, r, p):
        """Given vectors in Z^r spanning a rank-r Z_(p)-lattice K, return an exact r-vector Z_(p)-basis of K."""
        # Reduce rows of M = [vecs] using Z_(p)-row operations (pivot on minimum p-valuation in each col!)
        M = [[int(x) for x in v] for v in vecs]
        nrows = len(M)
        MOD = p**45
        row_idx = 0
        for col in range(r):
            best_v = 10**9
            bi = -1
            for i in range(row_idx, nrows):
                v = vp(M[i][col], p)
                if v < best_v:
                    best_v = v
                    bi = i
            assert bi != -1, "Rank deficit in p_adic_col_basis!"
            M[row_idx], M[bi] = M[bi], M[row_idx]
            piv = M[row_idx][col]
            u = piv // (p**best_v)
            for i in range(row_idx + 1, nrows):
                if M[i][col] != 0:
                    q = M[i][col] // (p**best_v)
                    for j in range(col, r):
                        M[i][j] = (u * M[i][j] - q * M[row_idx][j]) % MOD
            row_idx += 1
        # Wait: because we worked mod p^45, lift to exact integers (all valuations <= 15 << 45)!
        # Actually, to avoid ANY mod-p^45 issue in B_K.inv(), do exact integer elimination without MOD!
        M = [[int(x) for x in v] for v in vecs]
        row_idx = 0
        for col in range(r):
            best_v = 10**9
            bi = -1
            for i in range(row_idx, nrows):
                v = vp(M[i][col], p)
                if v < best_v:
                    best_v = v
                    bi = i
            M[row_idx], M[bi] = M[bi], M[row_idx]
            piv = M[row_idx][col]
            u = piv // (p**best_v)
            for i in range(row_idx + 1, nrows):
                if M[i][col] != 0:
                    q = M[i][col] // (p**best_v)
                    # Note: u is a p-adic unit, so replacing row i by u*row_i - q*row_piv is a Z_(p)-automorphism!
                    M[i] = [u * M[i][j] - q * M[row_idx][j] for j in range(r)]
            row_idx += 1
        return M[:r]

    M_sp = {0: sp.zeros(0, 0)}
    for m in range(1, H + 1):
        M_sp[m] = express_exact(S_bases[m], T_cols[m])

    for m in range(1, H + 1):
        # 1) Map (*E): X_{m-1} -> X_m
        shifted = [[0] * d + v for v in S_bases[m - 1]]
        A_E = express_exact(S_bases[m], shifted)
        ker_E, coker_E = ker_coker_invs(A_E, M_sp[m - 1], M_sp[m])
        assert ker_E == tors_invs(Fi[m]), f"Matlis ker(*E) mismatch at m={m}: {ker_E} != {tors_invs(Fi[m])}"
        assert coker_E == tors_invs(Fsi[H + 1 - m]), f"Matlis coker(*E) mismatch at m={m}: {coker_E} != {tors_invs(Fsi[H+1-m])}"

        # 2) Map (proj): X_m -> X_{m-1}
        projed = [v[: d * (m - 1)] for v in S_bases[m]]
        A_proj = express_exact(S_bases[m - 1], projed)
        ker_proj, coker_proj = ker_coker_invs(A_proj, M_sp[m], M_sp[m - 1])
        assert ker_proj == tors_invs(Qi[m - 1]), f"Matlis ker(proj) mismatch at m={m}: {ker_proj} != {tors_invs(Qi[m-1])}"
        assert coker_proj == tors_invs(Qsi[H - m]), f"Matlis coker(proj) mismatch at m={m}: {coker_proj} != {tors_invs(Qsi[H-m])}"


def run_suite_4():
    print("=== SUITE 4: Theorem L01-3 (Exact Invariant-Factor Verification of Four-Fold Matlis Duality Dictionary) ===")
    p = 2
    E = E_sym
    mats = [
        ("t37", sp.Matrix([[E, 0, 2], [0, E**2, 4 + 2 * E], [0, 0, E**2]])),
        ("P_kill4", sp.Matrix([[E, 0, 2, 0], [0, E**2, 16, 2 * E**2], [0, 0, E**2, 0], [0, 0, 0, E**3]])),
        ("P_{2,1}", build_Pn(2, p=2, k=1)),
        ("P_{3,1}", build_Pn(3, p=2, k=1)),
        ("P_tw", sp.Matrix([[1, 0, 0, 0], [E, -E**2, 0, 0], [2, -2*E, -E**3, 0], [0, 4, 2*E**2, E**3]])),
        ("nontri_3x3", sp.Matrix([[1, 0, 0], [E, 1, 0], [1, 2, 1]]) * sp.Matrix([[E, 2, 4], [0, E**2, 2 + 2*E], [0, 0, E**2]])),
    ]
    for name, P in mats:
        verify_matlis_fourfold(P, p=2)
    print(f"  [PASS] 4.1 Exact invariant-factor equalities ker(*E)=C, coker(*E)=C^*^v, ker(proj)=Q, coker(proj)=Q^*^v verified on {len(mats)} matrices.")


if __name__ == "__main__":
    run_suite_1()
    run_suite_2()
    run_suite_3()
    run_suite_4()
    print("\nALL 4 SUITES PASSED (EXIT CODE 0).")
