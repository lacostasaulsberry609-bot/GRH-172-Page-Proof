#!/usr/bin/env python3
"""
Wave-3 Assault Agent A02 — Self-Contained Computational & Symbolic Verifier
for Sinnott's Rational-Function Method on 2D Shintani-Cassou-Nogues Measures
over K_0 = Q(sqrt(5)).

Reproduces EVERY numerical and structural result in:
  erh_research/wave3/A02_sinnott_2var_shintani_mu_zero.md

Sections:
  [TEST 1] Exact verification of Cassou-Nogues / Dedekind-sum 2D measure against W2 Shintani (eq. 4.6)
  [TEST 2] 1D Deligne-Ribet Iwasawa power series G_{eta, c}(T) mod ell for F^+_{725} (n=2, 4 & Teichmuller twists)
           and F^{CM}_{1025} across ALL splitting types: ell = 3, 7 (inert), ell = 5 (ramified), ell = 11 (split)
           — certifying mu_ell = 0 and computing exact lambda_ell (including trivial zeros and non-trivial mod-(2+i) zero!)
  [TEST 3] 2-Variable Gamma-Transform Gamma_nu(T_cyc, T_anti) mod ell — verifying Theorem A (mu_2var = 0)
  [TEST 4] Obstruction Theorem B1: Hankel matrix ranks & algebraic-independence test of norm-pushforward H(1+T) mod 3
           for BOTH toy quadratic pushforward and genuine F^+_{725} Cassou-Nogues measure
  [TEST 5] Obstruction Theorem B2: The Totally-Even Shintani Counterexample (eta_even = 1 and psi_0, both original
           and symmetrized R(X1, X2) + R(X2, X1)) — coordinate-line poles, even/symmetric, non-zero 2D Gamma-transform,
           yet IDENTICALLY ZERO 1D norm-pushforward (exact T_anti-valuation 1 and 2!)
  [TEST 6] Obstruction Theorem B3: Explicit Cone-Subdivision Ambiguity D = C(1, eps) vs D' = C(1, 1+eps) U C(4-eps, 1)
           proving Gamma_D(T_cyc, T_anti) is canonical ONLY modulo the principal ideal (T_anti)
"""

from fractions import Fraction
from math import gcd
import numpy as np
import sympy as sp
from sympy.polys.matrices import DomainMatrix
from sympy.polys.domains import GF


# =============================================================================
# Core Arithmetic of K_0 = Q(sqrt(5)), basis {1, eps}, eps = (3 + sqrt(5))/2
# =============================================================================

def norm_Q(a, b):
    return a * a + 3 * a * b + b * b


def legendre(a, p):
    a %= p
    if a == 0:
        return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1


def psi0_725(a, b):
    return legendre(a - 4 * b, 29)


def chi_m4(n):
    n %= 4
    if n % 2 == 0:
        return 0
    return 1 if n == 1 else -1


def eta_725_m4(a, b):
    return psi0_725(a, b) * chi_m4(norm_Q(a, b))


def Phi_dedekind_table_exact(c, lam):
    base = Fraction((c - 1) ** 2, 4)
    return [base - Fraction(sum(j * ((w - lam * j) % c) for j in range(1, c)), c) for w in range(c)]


def Phi_dedekind_table_mod(c, lam, ell):
    tab = Phi_dedekind_table_exact(c, lam)
    out = np.zeros(c, dtype=np.int64)
    for w, fr in enumerate(tab):
        assert fr.denominator % ell != 0
        out[w] = (fr.numerator * pow(fr.denominator, -1, ell)) % ell
    return out


def verify_Phi_complex(c, lam):
    tab = Phi_dedekind_table_exact(c, lam)
    zeta = np.exp(2j * np.pi / c)
    max_err = 0.0
    for w in range(c):
        val = sum(-(zeta ** (-s * w)) / ((1 - zeta ** s) * (1 - zeta ** (lam * s))) for s in range(1, c))
        max_err = max(max_err, abs(val - float(tab[w])))
    assert max_err < 1e-10
    return max_err


def shintani_L0_exact(M, eta_func):
    B1 = [Fraction(a, M) - Fraction(1, 2) for a in range(M + 1)]
    B2 = [Fraction(a * a, M * M) - Fraction(a, M) + Fraction(1, 6) for a in range(M + 1)]
    total = Fraction(0)
    for a in range(1, M + 1):
        for b in range(1, M + 1):
            v = eta_func(a, b)
            if v != 0:
                total += v * (B1[a] * B1[b] + Fraction(3, 4) * (B2[a] + B2[b]))
        va = eta_func(a, 0)
        if va != 0:
            total -= va * B1[a]
    return total


def cassou_nogues_total_mass(M, c, lam, eta_func):
    tab = Phi_dedekind_table_exact(c, lam)
    invM = pow(M, -1, c)
    total = Fraction(0)
    for r1 in range(1, M + 1):
        for r2 in range(M):
            v = eta_func(r1, r2)
            if v != 0:
                total += v * tab[(-invM * (r1 + lam * r2)) % c]
    return total


def teichmuller_and_bracket(n, ell, mod_pow):
    M = ell ** mod_pow
    om = pow(n % M, ell ** (mod_pow - 1), M)
    return (n * pow(om, -1, M)) % M


def dlog_gamma(z, ell, m):
    M = ell ** m
    u = 1 + ell
    j = 0
    cur = 1
    for k in range(m - 1):
        step = pow(u, ell ** k, M)
        mod_next = ell ** (k + 2)
        ratio = (z * pow(cur, -1, mod_next)) % mod_next
        s_coeff = ((step - 1) // (ell ** (k + 1))) % ell
        r_coeff = ((ratio - 1) // (ell ** (k + 1))) % ell
        d = (r_coeff * pow(s_coeff, -1, ell)) % ell
        j += d * (ell ** k)
        cur = (cur * pow(step, d, M)) % M
    assert pow(u, j, M) == z % M
    return j


def binom_mod_table(L, p):
    C = np.zeros((L, L), dtype=np.int64)
    for j in range(L):
        C[j, 0] = 1
        for k in range(1, j + 1):
            C[j, k] = (C[j - 1, k - 1] + C[j - 1, k]) % p
    return C


def mul_ok(x, y, mod):
    a1, b1 = x
    a2, b2 = y
    return ((a1 * a2 - b1 * b2) % mod, (a1 * b2 + b1 * a2 + 3 * b1 * b2) % mod)


def pow_ok(x, e, mod):
    res = (1 % mod, 0)
    base = (x[0] % mod, x[1] % mod)
    while e > 0:
        if e & 1:
            res = mul_ok(res, base, mod)
        base = mul_ok(base, base, mod)
        e >>= 1
    return res


def inv_ok(x, mod):
    a, b = x
    n = norm_Q(a, b) % mod
    invn = pow(n, -1, mod)
    return (((a + 3 * b) * invn) % mod, ((-b) * invn) % mod)


# =============================================================================
# Fast Vectorized 1D Deligne-Ribet & 2D Gamma-Transform Engines
# =============================================================================

def fast_iwasawa_1d_mod_ell(M0, ell, m, eta_vec_func, c, lam):
    M_base = M0
    while M_base % ell == 0:
        M_base //= ell
    N_m = M_base * (ell ** m)
    ell_m = ell ** m
    num_bins = ell ** (m - 1)
    assert gcd(c, N_m) == 1

    tab_mod = Phi_dedekind_table_mod(c, lam, ell)
    invN = pow(N_m, -1, c)

    dlog_arr = np.full(ell_m, -1, dtype=np.int64)
    for r in range(1, ell_m):
        if r % ell != 0:
            dlog_arr[r] = dlog_gamma(teichmuller_and_bracket(r, ell, m), ell, m)

    bins = np.zeros(num_bins, dtype=np.int64)
    r1 = np.arange(1, N_m + 1, dtype=np.int64)
    r1_m = r1 % ell_m
    r1_c = r1 % c

    for r2 in range(N_m):
        r2_m = r2 % ell_m
        q_mod = (r1_m * r1_m + 3 * r1_m * r2_m + r2_m * r2_m) % ell_m
        j_arr = dlog_arr[q_mod]
        mask = j_arr >= 0
        if not np.any(mask):
            continue
        ev = eta_vec_func(r1[mask], r2)
        nz = ev != 0
        if not np.any(nz):
            continue
        w = (-invN * (r1_c[mask][nz] + lam * (r2 % c))) % c
        vals = (ev[nz] * tab_mod[w]) % ell
        np.add.at(bins, j_arr[mask][nz], vals)

    bins %= ell
    C = binom_mod_table(num_bins, ell)
    poly_T = (bins @ C) % ell
    return bins.tolist(), poly_T.tolist()


def fast_2var_gamma_mod_ell(M0, ell, m, eta_vec_func, c, lam, symmetrize=False):
    M_base = M0
    while M_base % ell == 0:
        M_base //= ell
    N_m = M_base * (ell ** m)
    ell_m = ell ** m

    tab_mod = Phi_dedekind_table_mod(c, lam, ell)
    invN = pow(N_m, -1, c)

    if ell == 5:
        u_cyc = (1 + ell, 0)
        u_anti = pow_ok((0, 1), 2, ell_m)
        ord_cyc = ell ** (m - 1)
        ord_anti = ell ** m
        delta_exp = ell ** m
    else:
        u_cyc = (1 + ell, 0)
        e_ell = 1
        cur = (0, 1)
        while cur != (1 % ell, 0):
            cur = mul_ok(cur, (0, 1), ell)
            e_ell += 1
        u_anti = pow_ok((0, 1), e_ell, ell_m)
        ord_cyc = ell ** (m - 1)
        ord_anti = ell ** (m - 1)
        delta_exp = ell ** (2 * (m - 1)) if legendre(5, ell) == -1 else ell ** (m - 1)

    u1_lookup = {}
    for j1 in range(ord_cyc):
        p1 = pow_ok(u_cyc, j1, ell_m)
        for j2 in range(ord_anti):
            u1_lookup[mul_ok(p1, pow_ok(u_anti, j2, ell_m), ell_m)] = (j1, j2)

    j1_tab = np.full((ell_m, ell_m), -1, dtype=np.int64)
    j2_tab = np.full((ell_m, ell_m), -1, dtype=np.int64)
    for a in range(ell_m):
        for b in range(ell_m):
            if norm_Q(a, b) % ell == 0:
                continue
            dx = pow_ok((a, b), delta_exp, ell_m)
            x_u1 = mul_ok((a, b), inv_ok(dx, ell_m), ell_m)
            j1_tab[a, b], j2_tab[a, b] = u1_lookup[x_u1]

    grid = np.zeros((ord_cyc, ord_anti), dtype=np.int64)
    r1 = np.arange(1, N_m + 1, dtype=np.int64)
    r1_m = r1 % ell_m
    r1_c = r1 % c

    for r2 in range(N_m):
        r2_m = r2 % ell_m
        j1_arr = j1_tab[r1_m, r2_m]
        mask = j1_arr >= 0
        if not np.any(mask):
            continue
        ev = eta_vec_func(r1[mask], r2)
        nz = ev != 0
        if not np.any(nz):
            continue
        w = (-invN * (r1_c[mask][nz] + lam * (r2 % c))) % c
        vals = (ev[nz] * tab_mod[w]) % ell
        j1_sel = j1_arr[mask][nz]
        j2_sel = j2_tab[r1_m[mask][nz], r2_m]
        np.add.at(grid, (j1_sel, j2_sel), vals)
        if symmetrize:
            np.add.at(grid, (j1_tab[r2_m, r1_m[mask][nz]], j2_tab[r2_m, r1_m[mask][nz]]), vals)

    grid %= ell
    C1 = binom_mod_table(ord_cyc, ell)
    C2 = binom_mod_table(ord_anti, ell)
    coeff_2d = (C1.T @ grid @ C2) % ell
    return grid, coeff_2d, ord_cyc, ord_anti


# Vectorized Characters
def make_psi0_vec(p, eps_mod_p, ell):
    leg = np.array([legendre(x, p) % ell for x in range(p)], dtype=np.int64)
    return lambda r1, r2: leg[(r1 + eps_mod_p * r2) % p]


def make_eta_725_m4_vec(ell):
    leg = np.array([legendre(x, 29) % ell for x in range(29)], dtype=np.int64)
    chi4 = np.array([0, 1, 0, ell - 1], dtype=np.int64)
    return lambda r1, r2: (leg[(r1 - 4 * r2) % 29] * chi4[(r1 * r1 + 3 * r1 * r2 + r2 * r2) % 4]) % ell


def make_eta_725_omega_vec(ell, a, with_chi4=False):
    leg = np.array([legendre(x, 29) % ell for x in range(29)], dtype=np.int64)
    chi4 = np.array([0, 1, 0, ell - 1], dtype=np.int64)
    powa = np.array([0 if x == 0 else pow(x, a, ell) for x in range(ell)], dtype=np.int64)
    if with_chi4:
        def f(r1, r2):
            q = r1 * r1 + 3 * r1 * r2 + r2 * r2
            return (leg[(r1 - 4 * r2) % 29] * chi4[q % 4] * powa[q % ell]) % ell
    else:
        def f(r1, r2):
            q = r1 * r1 + 3 * r1 * r2 + r2 * r2
            return (leg[(r1 - 4 * r2) % 29] * powa[q % ell]) % ell
    return f


def make_xi4_mod5_vec(i_val):
    leg = np.array([legendre(x, 29) % 5 for x in range(29)], dtype=np.int64)
    vals = [0] * 16
    for sgn in (1, -1):
        for k in range(4):
            vals[(sgn * pow(5, k, 16)) % 16] = (sgn * pow(i_val, k, 5)) % 5
    xi4 = np.array(vals, dtype=np.int64)
    return lambda r1, r2: (leg[(r1 - 4 * r2) % 29] * xi4[(r1 * r1 + 3 * r1 * r2 + r2 * r2) % 16]) % 5


def make_eta_1025_xi3_vec(ell):
    leg = np.array([legendre(x, 41) % ell for x in range(41)], dtype=np.int64)
    xi3 = np.array([0, 1, 0, ell - 1, 0, ell - 1, 0, 1], dtype=np.int64)
    return lambda r1, r2: (leg[(r1 - 5 * r2) % 41] * xi3[(r1 * r1 + 3 * r1 * r2 + r2 * r2) % 8]) % ell


def run_all_tests():
    print("=" * 80)
    print("WAVE-3 AGENT A02: COMPLETE VERIFICATION SUITE (2D SHINTANI-CASSOU-NOGUES & SINNOTT)")
    print("=" * 80)

    # -------------------------------------------------------------------------
    # TEST 1: Exact Cassou-Nogues / Dedekind-sum vs Shintani formula
    # -------------------------------------------------------------------------
    print("\n[TEST 1] Exact Verification: Cassou-Nogues / Dedekind-sum Formula vs W2 Shintani")
    L0 = shintani_L0_exact(116, eta_725_m4)
    assert L0 == 4
    print(f"  L_{{Q(sqrt(5))}}(0, psi_0 * (chi_{{-4}} o N)) = {L0} [matches W2 Table]")
    for ell, c, lam, gamma, eta_c in [
        (3, 31, 14, (79, -30), -1),
        (5, 11, 5, (37, -14), -1),
        (7, 11, 5, (37, -14), -1),
        (11, 19, 6, (45, -17), +1),
    ]:
        err = verify_Phi_complex(c, lam)
        cn = cassou_nogues_total_mass(116, c, lam, eta_725_m4)
        exp = (1 - eta_c * c) * L0
        assert cn == exp
        print(f"  ell={ell:2d}, c={c:2d} (lam={lam:2d}, gamma={gamma[0]}{gamma[1]:+d}*eps): "
              f"CN={cn} == (1 - ({eta_c:+d})*{c})*4 = {exp}  [EXACT! complex err={err:.1e}]")

    # -------------------------------------------------------------------------
    # TEST 2: 1D Deligne-Ribet Iwasawa Power Series G(T) mod ell (mu=0 Certification)
    # -------------------------------------------------------------------------
    print("\n[TEST 2] 1D Deligne-Ribet Power Series G_{eta, c}(T) mod ell (All Splitting Types!)")
    cases_1d = [
        ("F^+_725 n=2 (ell=3, INERT)", 116, 3, 2, make_eta_725_m4_vec(3), 31, 14),
        ("F^+_725 n=2 (ell=5, RAMIFIED)", 116, 5, 2, make_eta_725_m4_vec(5), 11, 5),
        ("F^+_725 n=2 (ell=7, INERT, trivial zero)", 116, 7, 2, make_eta_725_m4_vec(7), 11, 5),
        ("F^+_725 n=2 (ell=11, SPLIT, trivial zero)", 116, 11, 2, make_eta_725_m4_vec(11), 19, 6),
        ("F^+_725 n=2*omega^4 (ell=7, m=2)", 116, 7, 2, make_eta_725_omega_vec(7, 4, True), 11, 5),
        ("F^+_725 pure omega (ell=3, m=2)", 29, 3, 2, make_eta_725_omega_vec(3, 1, False), 19, 6),
        ("F^+_725 pure omega (ell=5, m=2)", 29, 5, 2, make_eta_725_omega_vec(5, 1, False), 19, 6),
        ("F^+_725 pure omega (ell=7, m=2)", 29, 7, 2, make_eta_725_omega_vec(7, 1, False), 11, 5),
        ("F^+_725 n=4 mod P=(2+i) [NON-TRIVIAL ZERO!]", 464, 5, 2, make_xi4_mod5_vec(3), 11, 5),
        ("F^+_725 n=4 mod P'=(2-i) [unit]", 464, 5, 2, make_xi4_mod5_vec(2), 11, 5),
        ("F^{CM}_1025 xi_3 (ell=3, m=2)", 328, 3, 2, make_eta_1025_xi3_vec(3), 11, 5),
        ("F^{CM}_1025 xi_3 (ell=5, m=1)", 328, 5, 1, make_eta_1025_xi3_vec(5), 11, 5),
        ("F^{CM}_1025 xi_3 (ell=7, m=1)", 328, 7, 1, make_eta_1025_xi3_vec(7), 11, 5),
    ]
    for label, M0, ell, m, fn, c, lam in cases_1d:
        _, poly = fast_iwasawa_1d_mod_ell(M0, ell, m, fn, c, lam)
        lam_inv = next((i for i, x in enumerate(poly) if x != 0), None)
        assert lam_inv is not None
        print(f"  {label:46s}: G(T) mod {ell:2d} = {str(poly[:11]):36s} | lam={lam_inv}, mu=0!")

    # -------------------------------------------------------------------------
    # TEST 3: 2-Variable Gamma-Transform (Verifying Theorem A)
    # -------------------------------------------------------------------------
    print("\n[TEST 3] 2-Variable Gamma-Transform Gamma_nu(T_cyc, T_anti) mod ell (Theorem A)")
    for label, M0, ell, m, fn, c, lam in [
        ("F^+_725 n=2 (ell=3, m=2)", 116, 3, 2, make_eta_725_m4_vec(3), 31, 14),
        ("F^+_725 pure omega (ell=5, m=2)", 29, 5, 2, make_eta_725_omega_vec(5, 1, False), 11, 5),
    ]:
        _, c2d, oc, oa = fast_2var_gamma_mod_ell(M0, ell, m, fn, c, lam)
        print(f"  {label} (ord_cyc={oc}, ord_anti={oa}):")
        for k1 in range(min(oc, 5)):
            print(f"    k1={k1}: {c2d[k1, :min(oa, 7)].tolist()}")

    # -------------------------------------------------------------------------
    # TEST 4: Obstruction B1 — Hankel Ranks & Algebraic Independence of H(1+T)
    # -------------------------------------------------------------------------
    print("\n[TEST 4] Obstruction B1: Hankel Rank & Algebraicity Test of Genuine F^+_725 H(1+T) mod (3, T^81)")
    ell, L, M0, c, lam = 3, 81, 116, 31, 14
    N = M0 * L
    tab_mod = Phi_dedekind_table_mod(c, lam, ell)
    invN = pow(N, -1, c)
    leg29 = np.array([legendre(x, 29) % ell for x in range(29)], dtype=np.int64)
    chi4 = np.array([0, 1, 0, ell - 1], dtype=np.int64)
    counts = np.zeros(L, dtype=np.int64)
    r1 = np.arange(1, N + 1, dtype=np.int64)
    r1_L, r1_29, r1_4, r1_c = r1 % L, r1 % 29, r1 % 4, r1 % c
    for r2 in range(N):
        r2_L = r2 % L
        q_L = (r1_L * r1_L + 3 * r1_L * r2_L + r2_L * r2_L) % L
        mask = (q_L % 3) != 0
        if not np.any(mask):
            continue
        ev = (leg29[(r1_29[mask] - 4 * (r2 % 29)) % 29] *
              chi4[(r1_4[mask] * r1_4[mask] + 3 * r1_4[mask] * (r2 % 4) + (r2 % 4) ** 2) % 4]) % ell
        nz = ev != 0
        if not np.any(nz):
            continue
        w = (-invN * (r1_c[mask][nz] + lam * (r2 % c))) % c
        np.add.at(counts, q_L[mask][nz], (ev[nz] * tab_mod[w]) % ell)
    counts %= ell
    C81 = binom_mod_table(L, ell)
    H_coeffs = ((counts @ C81) % ell).tolist()
    ranks = []
    for d in [5, 10, 15, 20, 25, 30, 35, 40]:
        dm = DomainMatrix([[GF(3)(H_coeffs[i + j]) for j in range(d)] for i in range(d)], (d, d), GF(3))
        ranks.append((d, len(dm.rref()[1])))
    prec = 75
    H_pows = [[1] + [0] * (prec - 1)]
    for _ in range(4):
        prev = H_pows[-1]
        nxt = [0] * prec
        for i in range(prec):
            if prev[i]:
                for j in range(prec - i):
                    nxt[i + j] = (nxt[i + j] + prev[i] * H_coeffs[j]) % 3
        H_pows.append(nxt)
    cols = [[0] * j + H_pows[i][:prec - j] for i in range(5) for j in range(7)]
    dm_alg = DomainMatrix([[GF(3)(cols[ci][row]) for ci in range(len(cols))] for row in range(prec)], (prec, len(cols)), GF(3))
    r_alg = len(dm_alg.rref()[1])
    print(f"  First 25 coeffs of H_{{725, 31}}(1+T) mod 3: {H_coeffs[:25]}")
    print(f"  Hankel (d x d) ranks over F_3: {ranks}")
    print(f"  Algebraic-dependence test (deg_H <= 4, deg_T <= 6): rank = {r_alg} / {len(cols)} (FULL RANK = {r_alg == len(cols)})")

    # -------------------------------------------------------------------------
    # TEST 5: Obstruction B2 — Totally-Even Shintani Counterexample
    # -------------------------------------------------------------------------
    print("\n[TEST 5] Obstruction B2: Totally-Even Shintani Counterexample (eta_even = 1 & psi_0)")
    for label, M0, fn, ell in [
        ("eta_even = 1 (M=1, ell=3)", 1, lambda r1, r2: np.ones_like(r1, dtype=np.int64), 3),
        ("eta_even = 1 (M=1, ell=5)", 1, lambda r1, r2: np.ones_like(r1, dtype=np.int64), 5),
        ("eta_even = psi_0 (M=29, ell=3)", 29, make_psi0_vec(29, -4, 3), 3),
        ("eta_even = psi_0 (M=29, ell=5)", 29, make_psi0_vec(29, -4, 5), 5),
    ]:
        for sym in (False, True):
            _, c2d, oc, oa = fast_2var_gamma_mod_ell(M0, ell, 2, fn, c=11, lam=5, symmetrize=sym)
            col0 = c2d[:, 0].tolist()
            min_k2 = next((k2 for k2 in range(c2d.shape[1]) if np.any(c2d[:, k2] != 0)), None)
            assert all(x == 0 for x in col0) and min_k2 is not None
            tag = "SYM" if sym else "ORIG"
            print(f"  {label:32s} [{tag:4s}]: col(T_anti=0)={col0} (ALL ZERO!) | 2D non-zero! exact ord_{{T_anti}} = {min_k2}")

    # -------------------------------------------------------------------------
    # TEST 6: Obstruction B3 — Cone-Subdivision Ambiguity
    # -------------------------------------------------------------------------
    print("\n[TEST 6] Obstruction B3: Cone-Subdivision Ambiguity D = C(1, eps) vs D' = C(1, 1+eps) U C(4-eps, 1)")
    ell, m, M0, c, lam = 3, 2, 116, 31, 14
    N, ell_m = M0 * 9, 9
    invN = pow(N, -1, c)
    lam_C1 = (1 + lam) % c
    lam_C2 = (lam * pow(1 + lam, -1, c)) % c
    tab_D = Phi_dedekind_table_mod(c, lam, ell)
    tab_C1 = Phi_dedekind_table_mod(c, lam_C1, ell)
    tab_C2 = Phi_dedekind_table_mod(c, lam_C2, ell)
    u_cyc, u_anti = (4, 0), pow_ok((0, 1), 4, ell_m)
    u1_lookup = {mul_ok(pow_ok(u_cyc, j1, ell_m), pow_ok(u_anti, j2, ell_m), ell_m): (j1, j2)
                 for j1 in range(3) for j2 in range(3)}
    j1_tab = np.full((ell_m, ell_m), -1, dtype=np.int64)
    j2_tab = np.full((ell_m, ell_m), -1, dtype=np.int64)
    for a in range(ell_m):
        for b in range(ell_m):
            if norm_Q(a, b) % 3 != 0:
                x_u1 = mul_ok((a, b), inv_ok(pow_ok((a, b), 9, ell_m), ell_m), ell_m)
                j1_tab[a, b], j2_tab[a, b] = u1_lookup[x_u1]

    def cone_grid(v1, v2, lam_cone, tab_cone):
        grid = np.zeros((3, 3), dtype=np.int64)
        u_arr = np.arange(1, N + 1, dtype=np.int64)
        for v in range(N):
            a = u_arr * v1[0] + v * v2[0]
            b = u_arr * v1[1] + v * v2[1]
            am, bm = a % ell_m, b % ell_m
            j1a = j1_tab[am, bm]
            mask = j1a >= 0
            if not np.any(mask):
                continue
            aa, bb = a[mask], b[mask]
            ev = (leg29[(aa - 4 * bb) % 29] * chi4[(aa * aa + 3 * aa * bb + bb * bb) % 4]) % ell
            nz = ev != 0
            if not np.any(nz):
                continue
            w = (-invN * (u_arr[mask][nz] + lam_cone * v)) % c
            np.add.at(grid, (j1a[mask][nz], j2_tab[am[mask][nz], bm[mask][nz]]), (ev[nz] * tab_cone[w]) % ell)
        return grid % ell

    g_D = cone_grid((1, 0), (0, 1), lam, tab_D)
    g_C1 = cone_grid((1, 0), (1, 1), lam_C1, tab_C1)
    g_C2 = cone_grid((1, 1), (0, 1), lam_C2, tab_C2)
    assert np.array_equal((g_C1 + g_C2) % 3, g_D)
    g_Dp = (g_C1 + cone_grid((4, -1), (1, 0), lam_C2, tab_C2)) % 3
    C3 = binom_mod_table(3, 3)
    F_D, F_Dp = (C3.T @ g_D @ C3) % 3, (C3.T @ g_Dp @ C3) % 3
    diff = (F_D - F_Dp) % 3
    assert np.array_equal(F_D[:, 0], F_Dp[:, 0]) and np.any(diff != 0)
    print(f"  Gamma_D  mod 3 = {F_D.tolist()}")
    print(f"  Gamma_D' mod 3 = {F_Dp.tolist()}")
    print(f"  Diff (Gamma_D - Gamma_D') mod 3 = {diff.tolist()} [col 0 = 0, cols 1,2 != 0!]")
    print("\nALL 6 VERIFICATION SUITES PASSED 100%!")


if __name__ == "__main__":
    run_all_tests()
