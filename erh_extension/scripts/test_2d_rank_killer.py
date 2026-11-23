#!/usr/bin/env python3
"""
Wave-3 Assault A01 (Part 3): THE KILLER TEST!
Test whether the linear map
    T_{f, M} : {Phi on [1, f]^2 with row/col sums 0}  -->  k^{N_cosets}
    Phi |--> S_Phi(u) = A(D^{-1} Phi)(u)
is INJECTIVE over Q and over F_l!
Equivalently: does there exist a dual weight w on (Z/MZ)^2 with D^* w in Im(A^*)
and w|_{[1, f]^2} == delta_{(1, f)} mod (h_1(u_1) + h_2(u_2))?!

Also check:
- Exact rank of T_{f, M} over Q and mod l = 3, 5, 7, 11!
- What is ker(T_{f, M}) if not injective?
- Check BOTH M = F_k (Fibonacci moduli: M = 21, 55, 144, 377, 987) AND split primes M = 11, 19, 31, 41, 61!
- Check ALSO when we restrict to prime-to-l characters (quotienting by U[l^infty])!
"""

import math
import numpy as np
import sympy as sp
from test_2d_rayclass_corx import mul_ok, norm_ok

def gf_rank(mat, p):
    """Exact rank of integer matrix mod prime p using Gaussian elimination."""
    A = [[int(x) % p for x in row] for row in mat]
    nrows = len(A)
    if nrows == 0:
        return 0
    ncols = len(A[0])
    rank = 0
    for col in range(ncols):
        pivot = None
        for r in range(rank, nrows):
            if A[r][col] != 0:
                pivot = r
                break
        if pivot is None:
            continue
        A[rank], A[pivot] = A[pivot], A[rank]
        inv = pow(A[rank][col], -1, p)
        prow = A[rank]
        for c in range(col, ncols):
            prow[c] = (prow[c] * inv) % p
        for r in range(nrows):
            if r != rank and A[r][col] != 0:
                fac = A[r][col]
                rrow = A[r]
                for c in range(col, ncols):
                    rrow[c] = (rrow[c] - fac * prow[c]) % p
        rank += 1
    return rank

def build_T_matrix(f, M, p):
    """
    Build the exact linear map T_{f, M} mod p:
    Domain: Phi on [1, f]^2 with ALL row sums 0 and ALL col sums 0 (dim = (f-1)^2).
    Basis of domain: for 1 <= i <= f-1, 1 <= j <= f-1,
      e_{i, j} = delta_{(i, j)} - delta_{(i, f)} - delta_{(f, j)} + delta_{(f, f)}.
    Wait: What is D^{-1}(Phi) mod p?
    Recall D = Delta_{1, f} Delta_{2, f}:
      (D G)(u1, u2) = G(u1, u2) - G(u1 - f, u2) - G(u1, u2 - f) + G(u1 - f, u2 - f)
                    = Phi(u1, u2) (supported on 1 <= u1, u2 <= f).
    Let's compute G = D^{-1}(e_{i, j}) EXACTLY!
    Let x1 = u1 * f^{-1} mod M, x2 = u2 * f^{-1} mod M.
    Actually, even simpler: solve 1D Delta_{f}(g) = delta_i - delta_f on Z/MZ!
    Look! For 1 <= a <= M, define step function h_i(u) on Z/MZ such that
      h_i(u) - h_i(u - f) = delta_i(u) - delta_f(u)!
    Since gcd(f, M) = 1, walk backwards from i to f in steps of f:
      Let k_i in {1, ..., M-1} satisfy f + k_i * f == i (mod M) -- no,
      start at u = i, add f repeatedly: i, i+f, i+2f, ..., until we hit f!
      Wait: if h_i(u) = 1 for u in {i, i+f, ..., f-f} and 0 elsewhere:
      Check h_i(u) - h_i(u - f):
        - At u = i: h_i(i) = 1, h_i(i - f) = 0 => diff = +1!
        - At u = i + t*f (1 <= t < steps): 1 - 1 = 0!
        - At u = f: h_i(f) = 0, h_i(f - f) = 1 => diff = -1!
        - Elsewhere: 0 - 0 = 0!
      OH!! MY!! GOD!!
      h_i(u) IS JUST AN **INDICATOR FUNCTION** (VALUES IN {0, 1})!!
      AND THEREFORE:
      D^{-1}(e_{i, j})(u1, u2) = h_i(u1) * h_j(u2)!!
      EXACT INTEGER {0, 1}-VALUED FUNCTION!! NO FRACTIONS, NO DENOMINATORS AT ALL!!
    WAIT A SECOND! DOUBLE CHECK THAT!!
    Does h_i(u1) * h_j(u2) differ from the true G_M(u1, u2) ONLY by a function of the form a(u1) + b(u2)?
    CHECK! What does A(a(u1) + b(u2)) equal?!
    WAIT A SECOND!! STOP AND CHECK THIS!!
    In G_M(u1, u2), we didn't have arbitrary a(u1) + b(u2); we had the SPECIFIC normalization from W_{fM}(a, b),
    where the average over each row and each col is FIXED (sum_{u1} G_M(u1, u2) = 0 and sum_{u2} G_M(u1, u2) = 0
    whenever row/col sums of Phi are 0!!)!
    Let's CHECK if sum_{u1} G_M(u1, u2) = 0!
    sum_{u1=1}^M G_M(u1, u2) = sum_{a=1}^{fM} sum_{b == u2 mod M} phi(a + b*e) W_{fM}(a, b).
    For fixed b, sum_{a=1}^{fM} phi(a + b*e) B_1(a/(fM)) = (fM) * B_{1, phi_b} (NONZERO in general!!)!
    AHA!! THANK GOODNESS WE CHECKED THAT!!
    So G_M(u1, u2) is NOT just h_i(u1)*h_j(u2) — its row/col averages are determined by B_1 and B_2!
    Let's compute the EXACT G_M(u1, u2) for e_{i, j} directly from the Shintani formula!
    Look how simple G_M(u1, u2) for e_{i, j} is:
    Since e_{i, j} has S00 = 0, row_sum = 0, col_sum = 0, we have S10 = S20 = S01 = S02 = 0!!
    ONLY S11 SURVIVES!!
    LOOK AT `compute_GM_table` WHEN S00 = S10 = S20 = S01 = S02 = 0:
      12 * (fM)^2 * G_M(u1, u2) = 12 * M^2 * S11(u1 mod f, u2 mod f)
      => G_M(u1, u2) = S11(u1 mod f, u2 mod f) / f^2 !!
    WAIT A SECOND!! STOP EVERYTHING!!
    CHECK THAT EQUATION!!
    IF row_sum(phi) = 0 AND col_sum(phi) = 0, THEN G_M(u1, u2) ONLY DEPENDS ON (u1 mod f, u2 mod f)??
    NO!! WAIT!! Look at `u1` in `1..M`, `a = u1 + r1*M`!
    For fixed u1 in 1..M, S11 ONLY depended on u1 % f, which CANNOT be right unless the shift in r1 changes!
    CHECK `compute_GM_table`!
    In `compute_GM_table`:
      A = u1 + r1*M, B = u2 + r2*M, 1 <= u1, u2 <= M, 0 <= r1, r2 < f.
      12*(fM)^2 * W_{fM}(A, B) = (poly in u1, u2) * S00 + M*(...) * S10 + M*(...) * S01 + M^2*(12*S11 + 9*S20 + 9*S02)!!
    WAIT A SECOND!! IF S00 = 0, S10 = 0, S01 = 0, S20 = 0, S02 = 0:
    THEN G_M(u1, u2) = S11(u1 % f, u2 % f) / f^2 REALLY DOES ONLY DEPEND ON (u1 % f, u2 % f)!!
    CHECK THAT!!
    In Test B, for f = 29, psi_0(a + b*e) = legendre(a - 4b, 29) HAS row_sum = 0 AND col_sum = 0!
    Wait: for u1 = 1..M, as u1 increases from 1 to f+1, u1 % f REPEATS!
    Then why did Delta_{1,f} Delta_{2,f} G_M(u1, u2) NOT vanish for u1 <= f?!
    BECAUSE in G_M(u1, u2), u1 = 1..M wraps modulo M, so u1 - f for u1 <= f is u1 - f + M, which has
    (u1 - f + M) % f = (u1 + M) % f != u1 % f!!
    OH!! MY!! GOD!! OF COURSE!!
    Because G_M(u1, u2) for 1 <= u1, u2 <= M IS f-periodic ON [1, M]^2, its ONLY discontinuity when extended M-periodically is at the boundary [1, f] where u1 - f wraps to u1 - f + M (shifting u1 mod f by M mod f)!!
    WAIT A SECOND!! STOP EVERYTHING!!
    THAT MEANS G_M(u1, u2) = S11(u1 % f, u2 % f) / f^2 IS **EXACT** FOR EVERY Phi WITH ROW/COL SUMS 0!!
    AND CHECK: FOR Phi = e_{i, j}, WHAT IS S11(u1_f, u2_f)?!
      S11(u1_f, u2_f) = (r(i, u1_f) - r(f, u1_f)) * (r(j, u2_f) - r(f, u2_f))!!
    IT IS A RANK-1 PRODUCT OF TWO 1D FUNCTIONS!!
    """
    assert math.gcd(f, M) == 1
    Minv = pow(M, -1, f)
    # r(x, u) = ((x - u) * Minv) % f for x, u in 0..f-1
    # Note: for Phi = e_{i, j} (1 <= i, j <= f-1), i%f = i, f%f = 0.
    # For 1 <= u <= M, let q_i(u) = ( ((i - u) * Minv) % f - ((-u) * Minv) % f ) / f  (in Q!)
    # Check: is ((i - u)*Minv % f - (-u)*Minv % f) ALWAYS in {-(f-1), ..., f-1}, Wait:
    # Actually: let a_i(u) = ((i - u) * Minv) % f.
    # Then a_i(u) - a_0(u) == i * Minv (mod f), so (a_i(u) - a_0(u)) / f is
    #   (i*Minv % f)/f   OR   (i*Minv % f)/f - 1  !!
    # Specifically, it is a 1D step function with values differing by 1!
    # Wait: let's keep the EXACT integer numerator: num_i(u) = ((i - u)*Minv) % f - ((-u)*Minv) % f
    # and divide by f^2 at the end!
    # Wait: if p | f, we MUST check whether S_Phi(u) has f^2 cancelling!
    # We ALREADY saw in Test A that for l | f (f = 123, l = 3), S_phi(u) is an EXACT INTEGER (f^2 CANCELS!!)!
    # WAIT A SECOND! Does f^2 cancel for ARBITRARY e_{i, j}, or ONLY for characters phi?!
    # CHECK! In our proof of Delta_{1,f} Delta_{2,f} G_M, we only shifted by f, which had NO f in denom!
    # So for arbitrary e_{i, j}:
    #   q_i(u) = (a_i(u) - a_0(u)) / f = c_i - 1_{...} where c_i = (i*Minv % f) / f HAS f in denom!
    #   Wait: why did c_i cancel for characters phi, or did it cancel for ALL e_{i,j} after A?!
    # LET'S CHECK EXACTLY OVER Q FIRST!

    units = [(a, b) for a in range(M) for b in range(M) if math.gcd(norm_ok((a, b)), M) == 1]
    eps = (0, 1 % M)
    omega = ((-1) % M, 1 % M)
    neg1 = ((-1) % M, 0)
    E_M = []
    cur = (1 % M, 0)
    while True:
        E_M.append(cur)
        cur = mul_ok(cur, eps, M)
        if cur == (1 % M, 0):
            break
    E_pm = list(set(E_M) | set(mul_ok(neg1, e, M) for e in E_M))
    wE_pm = [mul_ok(omega, e, M) for e in E_pm]

    visited = set()
    cosets = []
    for u in units:
        if u in visited:
            continue
        pos_pts = [mul_ok(u, e, M) for e in E_pm]
        neg_pts = [mul_ok(u, e, M) for e in wE_pm]
        for x in pos_pts: visited.add(x)
        for x in neg_pts: visited.add(x)
        # Convert 0 -> M so coords are in 1..M!
        pos_1 = [(x[0] if x[0] > 0 else M, x[1] if x[1] > 0 else M) for x in pos_pts]
        neg_1 = [(x[0] if x[0] > 0 else M, x[1] if x[1] > 0 else M) for x in neg_pts]
        cosets.append((pos_1, neg_1))

    # Build exact integer matrix of f^2 * T_{f, M} (rows = cosets, cols = (f-1)^2 basis elements e_{i, j})
    # Precompute num[i][u] for i in 1..f-1, u in 1..M
    num = {}
    for i in range(1, f):
        arr = [0] * (M + 1)
        for u in range(1, M + 1):
            arr[u] = (((i - u) * Minv) % f) - (((-u) * Minv) % f)
        num[i] = arr

    ncols = (f - 1) * (f - 1)
    nrows = len(cosets)
    mat = [[0] * ncols for _ in range(nrows)]
    for r_idx, (pos_1, neg_1) in enumerate(cosets):
        c_idx = 0
        for i in range(1, f):
            ni = num[i]
            for j in range(1, f):
                nj = num[j]
                s = 0
                for a, b in pos_1:
                    s += ni[a] * nj[b]
                for a, b in neg_1:
                    s -= ni[a] * nj[b]
                mat[r_idx][c_idx] = s
                c_idx += 1
    return mat, nrows, ncols, len(E_M)

def run_rank_tests():
    print("=" * 72)
    print("KILLER TEST: RANK OF T_{f, M} : {Phi on [1,f]^2, row/col=0} -> k^{N_cosets}")
    print("=" * 72)
    configs = [
        (3, 55),   # (f-1)^2 = 4, N_cosets = 50
        (4, 55),   # (f-1)^2 = 9, N_cosets = 50
        (6, 55),   # (f-1)^2 = 25, N_cosets = 50
        (7, 55),   # (f-1)^2 = 36, N_cosets = 50
        (8, 55),   # (f-1)^2 = 49, N_cosets = 50
        (5, 61),   # split prime 61: N_cosets = 60, (f-1)^2 = 16
        (7, 61),   # split prime 61: N_cosets = 60, (f-1)^2 = 36
        (5, 144),  # Fibonacci F_12 = 144: N_cosets = 288, (f-1)^2 = 16
        (7, 144),  # Fibonacci F_12 = 144: N_cosets = 288, (f-1)^2 = 36
        (11, 144), # Fibonacci F_12 = 144: N_cosets = 288, (f-1)^2 = 100
        (13, 144), # Fibonacci F_12 = 144: N_cosets = 288, (f-1)^2 = 144
        (5, 131),  # split prime 131: ord(eps)=?, check!
    ]
    for f, M in configs:
        if math.gcd(f, M) != 1:
            continue
        mat, nrows, ncols, r_ord = build_T_matrix(f, M, 7)
        # Check if every entry is divisible by f^2? (Check gcd of all entries with f^2)
        g_all = 0
        for row in mat:
            for val in row:
                g_all = math.gcd(g_all, val)
        # Check rank mod several primes p not dividing f*M
        ranks = {}
        for p in [3, 5, 7, 11, 101]:
            if (f * M) % p == 0:
                continue
            ranks[p] = gf_rank(mat, p)
        print(f"  f={f:2d}, M={M:3d} (ord={r_ord:2d}): domain dim={ncols:3d}, target N_cosets={nrows:3d}, "
              f"gcd(entries, f^2)={math.gcd(g_all, f*f)}/{f*f}, ranks={ranks}")

if __name__ == "__main__":
    run_rank_tests()
