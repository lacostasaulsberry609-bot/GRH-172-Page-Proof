#!/usr/bin/env python3
"""
Wave-3 Assault A01 (Part 2): Deep structural tests of 2D Ray-Class Twists on K0 = Q(sqrt(5)):
1. Actual Count II case with l | f:
   - l = 3, e = 1: phi = (chi_3 o N) * psi_0^CM (totally EVEN, f = 3 * 41 = 123, l | f!)
   - l = 5, e = 1: phi = (omega_5 o N) * psi_0^CM = legendre(a-b, 5) * psi_0^CM (totally EVEN, f = 5 * 41 = 205? Wait: N(w) = -1, omega_5(-1) = -1!)
   - l = 7, e = 3: phi = (chi_7 o N) * psi_0^CM (totally EVEN, f = 7 * 41 = 287!)
   - l = 13, e = 6: phi = (chi_13 o N) * psi_0 (totally EVEN, f = 13 * 29 = 377!)
   Wait: for l = 5, omega_5(x) has order 4 (values +-1, +-i), and omega_5(N(a+b*e)) = omega_5((a-b)^2) = legendre(a-b, 5)!!
   Check parity of legendre(a-b, 5): at omega = (-1, 1), a - b = -2, legendre(-2, 5) = -1! TOTALLY ODD!
   So legendre(a-b, 5) * psi_0^CM IS TOTALLY EVEN, with exact integer values {0, +-1}, conductor p_5 * p_41 (f = 5 * 41 = 205)!
2. Verify exact 2D mixed difference Delta_{1,f} Delta_{2,f} G_M(u1, u2) == 1_{[1,f]^2} * phi(u1 + u2*eps_+)!
3. Test genuine 2D non-cyclotomic double split prime ideals m = q1 * q2 (and triple q1*q2*q3)!
4. Check exact prime-to-l character nonvanishing for ALL of them, INCLUDING l | f!
"""

import math
from fractions import Fraction
import sympy as sp

from test_2d_rayclass_corx import (
    mul_ok, norm_ok, compute_GM_table, make_psi0_725, make_psi0_1025, split_prime_root
)

def compute_GM_table_fast(f, phi, M):
    """
    Fast O(f^2 + M^2) exact integer GM table using numpy if available, else fast Python.
    Even faster: compute S11 using 2D FFT? No, exact integers!
    Wait: S11(u1, u2) = sum_{r1, r2} r1 * r2 * phi(u1 + r1*M, u2 + r2*M).
    Notice that if phi(x, y) = phi1(x, y) mod f1 * phi2(x, y) mod f2 with gcd(f1, f2) = 1,
    still f <= 205 takes only ~0.3s in numpy int64 (wait: 205^3 = 8e6 ops in numpy takes 0.01s!).
    """
    import numpy as np
    assert math.gcd(f, M) == 1
    phi_tab = np.array([[phi(x, y) for y in range(f)] for x in range(f)], dtype=np.int64)
    S00 = int(phi_tab.sum())
    row_sum = phi_tab.sum(axis=1)  # shape (f,)
    col_sum = phi_tab.sum(axis=0)  # shape (f,)

    r = np.arange(f, dtype=np.int64)
    # idx[u, r] = (u + r*M) % f
    idx = (r[:, None] + r[None, :] * M) % f  # shape (f, f)
    S10 = (row_sum[idx] * r[None, :]).sum(axis=1)
    S20 = (row_sum[idx] * (r[None, :] ** 2)).sum(axis=1)
    S01 = (col_sum[idx] * r[None, :]).sum(axis=1)
    S02 = (col_sum[idx] * (r[None, :] ** 2)).sum(axis=1)

    # T[x, u2] = sum_{r2} r2 * phi_tab[x, (u2 + r2*M)%f]
    # Note: phi_tab[:, idx.T] has shape (f, f, f)? Too big? For f=205, 205^3 * 8B = 68MB!
    # Better: build matrix R[u, y] = ((y - u) * Minv) % f, then T = phi_tab @ R.T, S11 = R @ T!!
    # OH!! MATRIX MULTIPLICATION!! O(f^3) in BLAS takes 0.0005 SECONDS!!
    Minv = pow(M, -1, f)
    # For fixed u, r satisfies u + r*M == y (mod f) => r = ((y - u) * Minv) % f!
    y = np.arange(f, dtype=np.int64)
    R_mat = ((y[None, :] - y[:, None]) * Minv) % f  # shape (f, f): R_mat[u, y] = r
    # Check: T[x, u2] = sum_y phi_tab[x, y] * R_mat[u2, y] = (phi_tab @ R_mat.T)[x, u2]
    # S11[u1, u2] = sum_x R_mat[u1, x] * T[x, u2] = (R_mat @ phi_tab @ R_mat.T)[u1, u2]!!
    # Note: values <= f^4 ~ 205^4 ~ 1.8e9, fits easily in int64 (up to 9e18), use float64? NO, use int64/object!
    # For f <= 300, max entry of R_mat @ phi_tab @ R_mat.T is <= f^4 <= 8.1e9 << 9e18, 100% EXACT in int64!
    T_mat = phi_tab @ R_mat.T
    S11 = R_mat @ T_mat

    # Assemble G[u1 % M][u2 % M] as Python ints (exact, no overflow even for large M, f)
    G = [[0] * M for _ in range(M)]
    M2 = M * M
    fM = f * M
    c_const = 6 * fM * fM
    S10_l = [int(v) for v in S10]
    S20_l = [int(v) for v in S20]
    S01_l = [int(v) for v in S01]
    S02_l = [int(v) for v in S02]
    S11_l = [[int(v) for v in row] for row in S11]

    for u1 in range(1, M + 1):
        u1f = u1 % f
        u1m = u1 % M
        s10 = S10_l[u1f]
        s20 = S20_l[u1f]
        s11_row = S11_l[u1f]
        for u2 in range(1, M + 1):
            u2f = u2 % f
            val = (
                (12 * u1 * u2 + 9 * u1 * u1 + 9 * u2 * u2 - 15 * fM * (u1 + u2) + c_const) * S00
                + M * (12 * u2 + 18 * u1 - 15 * fM) * s10
                + M * (12 * u1 + 18 * u2 - 15 * fM) * S01_l[u2f]
                + M2 * (12 * s11_row[u2f] + 9 * s20 + 9 * S02_l[u2f])
            )
            G[u1m][u2 % M] = val
    return G, 12 * fM * fM

def test_l_divides_f():
    print("=" * 72)
    print("TEST A: ACTUAL COUNT II CASE WITH l | f (TOTALLY EVEN phi!)")
    print("=" * 72)
    cases = []
    # Case 1: l = 3, phi = (chi_3 o N) * psi_0^CM (f = 3*41 = 123, totally even!)
    def phi_3(a, b):
        v1 = (a - 5 * b) % 41
        if v1 == 0: return 0
        nm = (a * a + 3 * a * b + b * b) % 3
        if nm == 0: return 0
        return sp.legendre_symbol(v1, 41) * sp.legendre_symbol(nm, 3)
    cases.append((3, 123, phi_3, "(chi_3 o N) * psi_0^CM", [11, 17, 19]))

    # Case 2: l = 5, phi = (omega_5 o N) * psi_0^CM = legendre(a - b, 5) * psi_0^CM (f = 5*41 = 205, totally even!)
    def phi_5(a, b):
        v1 = (a - 5 * b) % 41
        if v1 == 0: return 0
        v5 = (a - b) % 5
        if v5 == 0: return 0
        return sp.legendre_symbol(v1, 41) * sp.legendre_symbol(v5, 5)
    cases.append((5, 205, phi_5, "(omega_5 o N) * psi_0^CM", [7, 13, 17]))

    # Case 3: l = 7, phi = (chi_7 o N) * psi_0^CM (f = 7*41 = 287, totally even!)
    def phi_7(a, b):
        v1 = (a - 5 * b) % 41
        if v1 == 0: return 0
        nm = (a * a + 3 * a * b + b * b) % 7
        if nm == 0: return 0
        return sp.legendre_symbol(v1, 41) * sp.legendre_symbol(nm, 7)
    cases.append((7, 287, phi_7, "(chi_7 o N) * psi_0^CM", [11, 13, 19]))

    for l, f, phi, desc, mods in cases:
        # Verify totally even: phi(-1) = 1 and phi(omega) = 1!
        assert phi(-1, 0) == 1 and phi(-1, 1) == 1, f"Parity check failed for {desc}"
        print(f"\n--- l = {l}, phi = {desc}, f = {f} (l | f! TOTALLY EVEN verified) ---")
        for M in mods:
            if math.gcd(M, f) != 1:
                continue
            G_phi, denom_phi = compute_GM_table_fast(f, phi, M)
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
            S_vals = []
            for u in units:
                if u in visited:
                    continue
                s = 0
                for e in E_pm:
                    x = mul_ok(u, e, M)
                    visited.add(x)
                    s += G_phi[x[0]][x[1]]
                for e in wE_pm:
                    x = mul_ok(u, e, M)
                    visited.add(x)
                    s -= G_phi[x[0]][x[1]]
                S_vals.append(Fraction(s, denom_phi))
            den_lcm = 1
            for x in S_vals:
                den_lcm = math.lcm(den_lcm, x.denominator)
            nz_mod_l = sum(1 for x in S_vals if x.denominator % l != 0 and (x.numerator % l) != 0)
            print(f"  M = {M}: |Cl^+|={len(units)//len(E_M)}, #odd_chars = {len(S_vals)}, den_lcm = {den_lcm}, "
                  f"S_phi(u) != 0 mod {l}: {nz_mod_l}/{len(S_vals)}")
            print(f"    S_phi values: {[str(x) for x in S_vals[:10]]}")

def test_2d_differencing():
    print("\n" + "=" * 72)
    print("TEST B: EXACT 2D MIXED DIFFERENCING Delta_{1,f} Delta_{2,f} G_M(u1, u2)")
    print("=" * 72)
    f, phi = make_psi0_725()
    M = 55  # Fibonacci F_10 = 55 > 29, ord(eps_+) = 10
    G, denom = compute_GM_table_fast(f, phi, M)
    mismatches = 0
    nonzero_box = 0
    nonzero_out = 0
    for u1 in range(1, M + 1):
        for u2 in range(1, M + 1):
            d = (G[u1 % M][u2 % M]
                 - G[(u1 - f) % M][u2 % M]
                 - G[u1 % M][(u2 - f) % M]
                 + G[(u1 - f) % M][(u2 - f) % M])
            val = Fraction(d, denom)
            expected = phi(u1, u2) if (u1 <= f and u2 <= f) else 0
            if val != expected:
                mismatches += 1
            if val != 0:
                if u1 <= f and u2 <= f: nonzero_box += 1
                else: nonzero_out += 1
    print(f"  f={f} (psi_0 of F^+_725), M={M}: mismatches={mismatches}, nonzero in [1,f]^2={nonzero_box}, outside={nonzero_out}")

    # ALSO verify Delta_{1,f} Delta_{2,f} G_M when l | f! (l=3, f=123, M=144? Let's use M=131 prime > 123!)
    def phi_3(a, b):
        v1 = (a - 5 * b) % 41
        if v1 == 0: return 0
        nm = (a * a + 3 * a * b + b * b) % 3
        if nm == 0: return 0
        return sp.legendre_symbol(v1, 41) * sp.legendre_symbol(nm, 3)
    f3 = 123
    M3 = 131
    G3, denom3 = compute_GM_table_fast(f3, phi_3, M3)
    mm3 = 0
    for u1 in range(1, M3 + 1):
        for u2 in range(1, M3 + 1):
            d = (G3[u1 % M3][u2 % M3]
                 - G3[(u1 - f3) % M3][u2 % M3]
                 - G3[u1 % M3][(u2 - f3) % M3]
                 + G3[(u1 - f3) % M3][(u2 - f3) % M3])
            val = Fraction(d, denom3)
            expected = phi_3(u1, u2) if (u1 <= f3 and u2 <= f3) else 0
            if val != expected:
                mm3 += 1
    print(f"  f={f3} (l=3 | f!!), M={M3}: mismatches={mm3}  <-- ZERO DENOMINATOR f EVEN WHEN l | f!!")

def test_double_split_ideals():
    print("\n" + "=" * 72)
    print("TEST C: GENUINE 2D NON-CYCLOTOMIC SPLIT IDEALS m = q_p1 * q_p2")
    print("=" * 72)
    f, phi = make_psi0_725()
    for p1, p2 in [(11, 31), (11, 41), (19, 31), (11, 61)]:
        r1 = split_prime_root(p1)[0]
        r2 = split_prime_root(p2)[0]
        M = p1 * p2
        if math.gcd(M, f) != 1:
            continue
        w1, w2 = (r1 - 1) % p1, (r2 - 1) % p2
        E_M = []
        c1, c2 = 1, 1
        while True:
            E_M.append((c1, c2))
            c1 = (c1 * r1) % p1
            c2 = (c2 * r2) % p2
            if (c1, c2) == (1, 1):
                break
        r = len(E_M)
        E_pm = list(set(E_M) | set(((-x) % p1, (-y) % p2) for x, y in E_M))
        if (w1, w2) in E_pm:
            print(f"  m = q_{p1}*q_{p2}: no totally odd chars")
            continue
        wE_pm = [((w1 * x) % p1, (w2 * y) % p2) for x, y in E_pm]

        G_phi, denom_phi = compute_GM_table_fast(f, phi, M)
        bucket = [[0] * p2 for _ in range(p1)]
        for u1 in range(M):
            u1_p1 = u1 % p1
            u1_p2 = u1 % p2
            grow = G_phi[u1]
            for u2 in range(M):
                x1 = (u1_p1 + u2 * r1) % p1
                if x1 == 0: continue
                x2 = (u1_p2 + u2 * r2) % p2
                if x2 == 0: continue
                bucket[x1][x2] += grow[u2]

        visited = set()
        S_vals = []
        for x1 in range(1, p1):
            for x2 in range(1, p2):
                if (x1, x2) in visited: continue
                s = 0
                for e1, e2 in E_pm:
                    pt = ((x1 * e1) % p1, (x2 * e2) % p2)
                    visited.add(pt)
                    s += bucket[pt[0]][pt[1]]
                for e1, e2 in wE_pm:
                    pt = ((x1 * e1) % p1, (x2 * e2) % p2)
                    visited.add(pt)
                    s -= bucket[pt[0]][pt[1]]
                S_vals.append(Fraction(s, denom_phi))
        den_lcm = 1
        for x in S_vals:
            den_lcm = math.lcm(den_lcm, x.denominator)
        nz3 = sum(1 for x in S_vals if x.numerator % 3 != 0)
        nz5 = sum(1 for x in S_vals if x.numerator % 5 != 0)
        nz7 = sum(1 for x in S_vals if x.numerator % 7 != 0)
        print(f"  m = q_{p1}*q_{p2} (Nm={M}): |U|={(p1-1)*(p2-1)}, ord(eps)={r}, |Cl^+|={(p1-1)*(p2-1)//r}, "
              f"#odd={len(S_vals)}, den_lcm={den_lcm}")
        print(f"    S_phi!=0 mod 3: {nz3}/{len(S_vals)}, mod 5: {nz5}/{len(S_vals)}, mod 7: {nz7}/{len(S_vals)}")
        print(f"    Sample S_phi: {[str(x) for x in S_vals[:10]]}")

if __name__ == "__main__":
    test_l_divides_f()
    test_2d_differencing()
    test_double_split_ideals()
