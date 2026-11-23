#!/usr/bin/env python3
r"""
Verification script for Wave-16 N01:
  - Theorem N01-1: Elementary 2-adic Kronecker rk_2-reflection & Deligne-Ribet 2-adic L-function normalization
  - Theorem N01-2: Brauer-Artin Analytic mu_ell-Descent Theorem & Finite Group Catalog
                   (A_5, S_5, PSL_2(F_7) [sharp obstruction], PSL_2(F_8), A_6, S_6, PSL_2(F_11),
                    plus symbolic proof for the universal infinite family PSL_2(F_{2^f}))
  - Theorem N01-3: First Unconditional (Zero-GRH, Rigorously Error-Bounded) Certifications of
                   Totally Real A_5 and S_5 Fields with mu_2(\widetilde{F^+}(i)) = 0:
                     1. Pure Regime-A A_5(10931^2) = A_5(17^2 * 643^2)
                     2. Single-Prime Pure Regime-A A_5(11699^2)
                     3. Minimal Totally Real S_5(7^3 * 11^3 * 41^2) = S_5(767431973) (Ford-Pohst et al. 1998)
                   Plus partial certification of Pure Regime-A S_5(137 * 191^2) F_5^+,
                   and algebraic/cohomological verification of infinite non-solvable towers
                   (P_2 x A_5, C_2^{4m} rtimes A_5, and Serre Witt invariant for 2.A_5 = SL_2(F_5)).

NOTE: This script verifies finite instances and explicit numerical/algebraic certificates.
General theorems (N01-1, N01-2, universal PSL_2(F_{2^f}), Fukuda 1994, infinite Chebotarev towers)
are proved analytically/algebraically in erh_research/wave16/N01_brauer_artin_analytic_mu2_descent_a5_s5.md.
"""

import math
import sys
import time
from itertools import permutations
import numpy as np
from scipy.special import loggamma
import mpmath as mp
import sympy as sp
from sympy import Poly, Symbol, Matrix, Rational, factorint, nextprime
from sympy.combinatorics import Permutation, PermutationGroup
from sympy.functions.combinatorial.numbers import jacobi_symbol, legendre_symbol

x = Symbol('x')


# =============================================================================
# SHARED RIGOROUS ANALYTIC L-VALUE ENGINE (ZERO GRH, ALL 4 ERROR TERMS PROVED)
# =============================================================================

def zeta_upper_midpoint(tau: float, M: int = 5000) -> float:
    """
    Rigorous elementary upper bound on zeta(tau) for tau > 1 via Jensen's inequality
    on the convex decreasing function t -> t^{-tau}:
        k^{-tau} <= int_{k-1/2}^{k+1/2} t^{-tau} dt  for every integer k >= 1.
    Summing k = M+1..inf yields sum_{k>M} k^{-tau} <= (M + 1/2)^{1-tau} / (tau - 1).
    """
    ks = np.arange(1, M + 1, dtype=np.float64)
    return float(np.sum(ks ** (-tau))) + ((M + 0.5) ** (1.0 - tau)) / (tau - 1.0)


def vectorized_nroots_mod_primes(poly_coeffs, primes_arr):
    """
    Exact count of F_p-roots of a monic integer polynomial `poly_coeffs` (high-to-low)
    for every prime p in `primes_arr` (with p < 10^9 so d*p^2 < 2^63),
    computing x^p mod f(x) in parallel via NumPy int64, followed by exact deg(gcd(f, x^p - x)).
    """
    d = len(poly_coeffs) - 1
    out = np.zeros(len(primes_arr), dtype=np.int32)
    chunk = 50000
    c_rev = list(reversed(poly_coeffs))
    for s0 in range(0, len(primes_arr), chunk):
        P = primes_arr[s0:s0 + chunk].astype(np.int64)
        nP = len(P)
        fl = [np.mod(c, P) for c in c_rev[:d]]
        max_bits = int(P[-1]).bit_length()
        xp = [np.zeros(nP, dtype=np.int64) for _ in range(d)]
        xp[0][:] = 1
        base = [np.zeros(nP, dtype=np.int64) for _ in range(d)]
        base[1][:] = 1
        for bit in range(max_bits):
            mask = ((P >> bit) & 1).astype(bool)
            if np.any(mask):
                Pm = P[mask]
                flm = [f[mask] for f in fl]
                xpm = [v[mask] for v in xp]
                bm = [v[mask] for v in base]
                pr = [np.zeros(len(Pm), dtype=np.int64) for _ in range(2 * d - 1)]
                for i in range(d):
                    xi = xpm[i]
                    for j in range(d):
                        pr[i + j] = (pr[i + j] + xi * bm[j]) % Pm
                for i in range(2 * d - 2, d - 1, -1):
                    ci = pr[i]
                    for j in range(d):
                        pr[i - d + j] = (pr[i - d + j] - ci * flm[j]) % Pm
                for i in range(d):
                    xp[i][mask] = pr[i]
            if bit + 1 < max_bits:
                pr = [np.zeros(nP, dtype=np.int64) for _ in range(2 * d - 1)]
                for i in range(d):
                    bi = base[i]
                    pr[2 * i] = (pr[2 * i] + bi * bi) % P
                    for j in range(i + 1, d):
                        pr[i + j] = (pr[i + j] + 2 * bi * base[j]) % P
                for i in range(2 * d - 2, d - 1, -1):
                    ci = pr[i]
                    for j in range(d):
                        pr[i - d + j] = (pr[i - d + j] - ci * fl[j]) % P
                base = pr[:d]
        xp[1] = (xp[1] - 1) % P
        xp_mat = np.stack(xp, axis=1)
        A_mat = np.stack([np.mod(c, P) for c in poly_coeffs], axis=1)
        res = np.zeros(nP, dtype=np.int32)
        for idx in range(nP):
            p = int(P[idx])
            B = [int(v) for v in xp_mat[idx][::-1]]
            while B and B[0] == 0:
                B.pop(0)
            if not B:
                res[idx] = d
                continue
            A = [int(v) for v in A_mat[idx]]
            while B:
                invB = pow(B[0], p - 2, p)
                while len(A) >= len(B):
                    fac = (A[0] * invB) % p
                    for i in range(len(B)):
                        A[i] = (A[i] - fac * B[i]) % p
                    while A and A[0] == 0:
                        A.pop(0)
                A, B = B, A
            res[idx] = len(A) - 1
        out[s0:s0 + chunk] = res
    return out


def compute_rE_and_zeta_ub(poly_coeffs, N_max: int, taus, special_primes=None):
    """
    Compute exact odd-norm ideal counts r_E(n) for odd n <= N_max for a monogenic
    (or `special_primes`-corrected) number field E = Q[x]/(poly_coeffs), AND simultaneously
    compute a rigorous upper bound Z_ub(tau) >= zeta_E^odd(tau) using ALL odd primes p <= N_max.
    """
    d = len(poly_coeffs) - 1
    r = np.zeros(N_max + 1, dtype=np.int32)
    r[1] = 1
    sieve = np.ones(N_max + 1, dtype=bool)
    sieve[0:2] = False
    sieve[2::2] = False
    lim = math.isqrt(N_max)
    for p in range(3, lim + 1, 2):
        if sieve[p]:
            sieve[p * p::2 * p] = False
    primes = np.nonzero(sieve)[0]
    D_poly = abs(int(Poly(poly_coeffs, x, domain='ZZ').discriminant()))
    special_primes = special_primes or {}

    # Rigorous starting upper bound: prod_{p odd} (1 - p^{-tau})^{-d} = ((1 - 2^{-tau}) zeta(tau))^d
    log_Zub = {t: d * math.log((1.0 - 2.0 ** (-t)) * zeta_upper_midpoint(t)) for t in taus}

    small_p = primes[primes <= lim]
    big_p = primes[primes > lim]
    big_special = [int(p) for p in big_p if (int(p) in special_primes) or (D_poly % int(p) == 0)]
    big_reg = big_p[np.array(
        [(int(p) not in special_primes) and (D_poly % int(p) != 0) for p in big_p], dtype=bool
    )]

    for p in list(map(int, small_p)) + big_special:
        if p in special_primes:
            f_list = [fi for fi, _ in special_primes[p]]
        else:
            f_list = [g.degree() for g, _ in Poly(poly_coeffs, x, modulus=p).factor_list()[1]]
        for t in taus:
            log_Zub[t] += d * math.log(1.0 - p ** (-t)) - sum(
                math.log(1.0 - p ** (-fi * t)) for fi in f_list
            )
        kmax = int(math.log(N_max) / math.log(p)) + 1
        while p ** kmax > N_max:
            kmax -= 1
        loc = [0] * (kmax + 1)
        loc[0] = 1
        for fi in f_list:
            for k in range(fi, kmax + 1):
                loc[k] += loc[k - fi]
        r_old = r.copy()
        pk = p
        for k in range(1, kmax + 1):
            ck = loc[k]
            if ck:
                ms = np.arange(1, N_max // pk + 1, 2)
                ms = ms[(ms % p) != 0]
                r[ms * pk] += ck * r_old[ms]
            pk *= p

    if len(big_reg) > 0:
        nr = vectorized_nroots_mod_primes(poly_coeffs, big_reg)
        pf = big_reg.astype(np.float64)
        rem_pairs = (d - nr) // 2
        for t in taus:
            pt = pf ** (-t)
            # For p > sqrt(N_max), exact degree-1 count is nr; remaining degree (d - nr) has all f_P >= 2,
            # so prod_{P|p, f_P>=2} (1 - p^{-f_P t})^{-1} <= (1 - p^{-2t})^{-floor((d-nr)/2)}.
            log_Zub[t] += float(np.sum((d - nr) * np.log1p(-pt) - rem_pairs * np.log1p(-pt * pt)))
        for idx in np.nonzero(nr)[0]:
            p = int(big_reg[idx])
            m_max = N_max // p
            r[p:m_max * p + 1:2 * p] = int(nr[idx]) * r[1:m_max + 1:2]

    # Add 1e-13 relative safety factor on exp(log_Zub) to guard against float64 log/exp rounding.
    Zub = {t: math.exp(log_Zub[t]) * (1.0 + 1e-13) for t in taus}
    return r, Zub


def make_weight_kernel(d: int, shift: float, c_re: float, h: float = 0.045, T_max: float = 18.0):
    K = int(math.ceil(T_max / h))
    ts = np.arange(K + 1) * h
    zs = c_re + 1j * ts
    w = np.ones(K + 1)
    w[0] = 0.5
    return h, c_re, (h / math.pi) * w * np.exp(d * loggamma((zs + shift) / 2.0)) / zs


def eval_W_horner(ys, d: int, h: float = 0.045, T_max: float = 18.0):
    """
    Evaluate W_0(y) and y^{-1} W_1(y) using split contours:
      y < 1: c = -0.5 for W_0 (+ residue pi^{d/2}), c = -1.0 for W_1 (+ residue 1)
      y >= 1: c = +3.0 for both W_0 and W_1
    with Horner's rule on z = exp(-i h log y) (|z| = 1).
    """
    _, c0m, k0m = make_weight_kernel(d, 1.0, -0.5, h=h, T_max=T_max)
    _, c1m, k1m = make_weight_kernel(d, 2.0, -1.0, h=h, T_max=T_max)
    _, c0p, k0p = make_weight_kernel(d, 1.0, +3.0, h=h, T_max=T_max)
    _, c1p, k1p = make_weight_kernel(d, 2.0, +3.0, h=h, T_max=T_max)

    def ec_pair(y_sub, c0, k0, c1, k1):
        out0 = np.empty_like(y_sub)
        out1 = np.empty_like(y_sub)
        K = len(k0) - 1
        chunk = 120000
        for i in range(0, len(y_sub), chunk):
            ys_c = y_sub[i:i + chunk]
            z = np.exp((-1j * h) * np.log(ys_c))
            a0 = np.full(len(ys_c), k0[K], dtype=np.complex128)
            a1 = np.full(len(ys_c), k1[K], dtype=np.complex128)
            for k in range(K - 1, -1, -1):
                a0 = a0 * z + k0[k]
                a1 = a1 * z + k1[k]
            out0[i:i + chunk] = (ys_c ** (-c0)) * a0.real
            out1[i:i + chunk] = (ys_c ** (-c1)) * a1.real
        return out0, out1

    W0 = np.empty_like(ys)
    W1y = np.empty_like(ys)
    ml = ys < 1.0
    mg = ~ml
    if np.any(ml):
        yl = ys[ml]
        v0, v1 = ec_pair(yl, c0m, k0m, c1m, k1m)
        W0[ml] = (math.pi ** (d / 2.0)) + v0
        W1y[ml] = (1.0 / yl) + v1 / yl
    if np.any(mg):
        yg = ys[mg]
        v0, v1 = ec_pair(yg, c0p, k0p, c1p, k1p)
        W0[mg] = v0
        W1y[mg] = v1 / yg
    return W0, W1y


def rigorous_quad_error_per_term(d: int, A: float, h: float = 0.045, T_max: float = 18.0):
    """
    Compute provable per-term upper bounds (eps_trunc_lt, eps_trunc_ge, eps_trap_lt, eps_trap_ge)
    for |W_0(y) - W_0^{num}(y)| + |y^{-1} W_1(y) - y^{-1} W_1^{num}(y)|
    for y = n/A < 1 (with y >= 1/A) and y >= 1, using our closed-form Weierstrass-product
    and Trefethen-Weideman strip bounds.
    """
    S0 = T_max / 2.0
    assert S0 >= 8.0
    kappa_d = 1.0 if d == 1 else (math.sqrt(math.pi) * math.gamma((d - 1) / 2.0) / (2.0 * math.gamma(d / 2.0)))

    # 1. Truncation bounds (|t| > T_max, s = t/2 >= S0):
    # y < 1: W_0 (a=1/4, |Gamma(1/4+is)| <= sqrt(2)*Gamma(1/4)*e^{-pi s/2}), W_1 (a=1/2, <= sqrt(2pi)*e^{-pi s/2})
    t0_lt = (2.0 * ((math.sqrt(2.0) * math.gamma(0.25)) ** d) / (d * math.pi * math.pi * S0)) * math.exp(-d * math.pi * S0 / 2.0)
    t1_lt = (2.0 * ((math.sqrt(2.0 * math.pi)) ** d) / (d * math.pi * math.pi * S0)) * math.exp(-d * math.pi * S0 / 2.0)
    # y >= 1: W_0 (a=2, |Gamma(2+is)| <= 2.53*s^{3/2}*e^{-pi s/2}), W_1 (a=5/2, <= 2.60*s^2*e^{-pi s/2})
    t0_ge = (4.0 * ((2.53 ** d) * (S0 ** (1.5 * d))) / (d * math.pi * math.pi * S0)) * math.exp(-d * math.pi * S0 / 2.0)
    t1_ge = (4.0 * ((2.60 ** d) * (S0 ** (2.0 * d))) / (d * math.pi * math.pi * S0)) * math.exp(-d * math.pi * S0 / 2.0)

    # 2. Trapezoidal discretization bounds (Trefethen-Weideman 2014, Thm. 5.1):
    # Integral bound on M_+(alpha) + M_-(alpha) using |Gamma(a + is)| <= Gamma(a)*(1 + s^2/a^2)^{-1/2}:
    def strip_M(a_val, c_abs, y_pow_ub):
        # (1/(2pi)) * int_{-inf}^inf |Gamma(a + i t/2)|^d dt / c_abs <= (2 / (pi * c_abs)) * Gamma(a)^d * a * kappa_d * y_pow_ub
        if d == 1:
            # For d = 1, use reflection/Weierstrass exponential bound int_0^inf e^{-pi s/2} ds = 2/pi:
            if a_val <= 0.5:
                return (2.0 / (math.pi * c_abs)) * math.sqrt(2.0) * math.gamma(a_val) * (2.0 / math.pi) * y_pow_ub
            else:
                return (2.0 / (math.pi * c_abs)) * (math.gamma(a_val) * 10.0) * y_pow_ub
        return (2.0 / (math.pi * c_abs)) * (math.gamma(a_val) ** d) * a_val * kappa_d * y_pow_ub

    # W_0, y < 1: c = -0.5, alpha = 0.35 -> c +- alpha in {-0.85, -0.15}, a in {0.075, 0.425}, y^{-(-0.85)} <= 1
    tr0_lt = (strip_M(0.075, 0.85, 1.0) + strip_M(0.425, 0.15, 1.0)) / (math.exp(2.0 * math.pi * 0.35 / h) - 1.0)
    # y^{-1} W_1, y < 1: c = -1.0, alpha = 0.60 -> c +- alpha in {-1.60, -0.40}, a in {0.20, 0.80},
    # factor y^{-1} * y^{-(c +- alpha)} <= y^{-0.60} <= A^{0.60}
    tr1_lt = (strip_M(0.20, 1.60, 1.0) + strip_M(0.80, 0.40, A ** 0.60)) / (math.exp(2.0 * math.pi * 0.60 / h) - 1.0)
    # W_0, y >= 1: c = 3.0, alpha = 2.0 -> c +- alpha in {1.0, 5.0}, a in {1.0, 3.0}, y^{-(c +- alpha)} <= 1
    tr0_ge = (strip_M(1.0, 1.0, 1.0) + strip_M(3.0, 5.0, 1.0)) / (math.exp(2.0 * math.pi * 2.0 / h) - 1.0)
    # y^{-1} W_1, y >= 1: c = 3.0, alpha = 2.0 -> a in {1.5, 3.5}, y^{-1-(c +- alpha)} <= 1
    tr1_ge = (strip_M(1.5, 1.0, 1.0) + strip_M(3.5, 5.0, 1.0)) / (math.exp(2.0 * math.pi * 2.0 / h) - 1.0)

    return (t0_lt + t1_lt), (t0_ge + t1_ge), (tr0_lt + tr1_lt), (tr0_ge + tr1_ge)


def check_monogenic_and_regime(poly_coeffs, expected_D, ram_expected_info=None):
    """Verify irreducibility, total reality, Dedekind p-maximality (monogenicity), and ramification."""
    f = Poly(poly_coeffs, x, domain='ZZ')
    assert f.is_irreducible, f"Polynomial {poly_coeffs} is reducible!"
    D = int(f.discriminant())
    assert D == expected_D, f"disc={D} != expected {expected_D}"
    # Verify total reality via real roots count (high-precision Sturm/real_roots)
    n_real = len(f.real_roots())
    assert n_real == f.degree(), f"Not totally real: {n_real} != {f.degree()}"
    # Dedekind criterion at every prime p^2 | D
    fac = factorint(D)
    patterns = {}
    for p, vp in sorted(fac.items()):
        fp = Poly(poly_coeffs, x, modulus=p)
        fl = fp.factor_list()[1]
        pat = sorted([(gi.degree(), ei) for gi, ei in fl])
        patterns[p] = (vp, pat)
        if vp >= 2:
            g_int = Poly(1, x, domain='ZZ')
            h_int = Poly(1, x, domain='ZZ')
            for gi, ei in fl:
                gi_z = Poly([int(c) % p for c in gi.all_coeffs()], x, domain='ZZ')
                g_int *= gi_z
                if ei > 1:
                    h_int *= (gi_z ** (ei - 1))
            M = Poly([int(c) // p for c in (f - g_int * h_int).all_coeffs()], x, domain='ZZ')
            gg = sp.gcd(
                sp.gcd(Poly(g_int.all_coeffs(), x, modulus=p), Poly(h_int.all_coeffs(), x, modulus=p)),
                Poly(M.all_coeffs(), x, modulus=p),
            )
            assert gg.degree() == 0, f"Not {p}-maximal for {poly_coeffs}!"
    # Check Frobenius cycle types for unramified primes p <= 250
    cts = set()
    p = 2
    while p <= 250:
        if D % p != 0:
            cts.add(tuple(sorted([g.degree() for g, _ in Poly(poly_coeffs, x, modulus=p).factor_list()[1]])))
        p = nextprime(p)
    pat2 = tuple(sorted([g.degree() for g, _ in Poly(poly_coeffs, x, modulus=2).factor_list()[1]]))
    return D, patterns, pat2, cts


def certify_field_values(name, poly_coeffs, D_field, N_max, do_f16=False, h=0.045, T_max=18.0):
    """
    Fully rigorous zero-GRH certification of N_4, N_8 (and optionally g(i-1)/2 in Z[i])
    for a monogenic totally real field E of degree d in {5, 6}, gcd(D_field, 2) = 1.
    """
    d = len(poly_coeffs) - 1
    taus = [1.5, 1.8, 2.0, 2.2, 2.5, 2.8, 3.0]
    t0 = time.time()
    r, Zub = compute_rE_and_zeta_ub(poly_coeffs, N_max, taus)
    nz = np.nonzero(r)[0]
    rn = r[nz].astype(np.float64)
    nf = nz.astype(np.float64)
    # Rigorous upper bound on sum_{n > N_max, 2 nmid n} r_E(n) n^{-t}:
    rem_Z = {}
    for t in taus:
        SN = float(np.sum(rn * (nf ** (-t))))
        # Guard against float64 rounding in SN by subtracting 1e-13 * SN
        diff = Zub[t] - SN * (1.0 - 1e-13)
        assert diff > 0.0, f"Upper bound failure at tau={t}"
        rem_Z[t] = diff
    t_sieve = time.time() - t0

    results = {}
    # Evaluate f = 4 and f = 8
    for fc, mexp in [(4, 2 - d), (8, 1 - d)]:
        A = math.sqrt(D_field * (fc ** d) / (math.pi ** d))
        N_cut = N_max if (fc == 8 and not do_f16) else min(N_max, max(int(30 * A), min(N_max, 1000000)))
        if fc == 8 and do_f16:
            N_cut = min(N_max, int(15 * A))
        mask = nz <= N_cut
        nz_c, rn_c, nf_c = nz[mask], rn[mask], nf[mask]
        ys_c = nf_c / A
        W0, W1y = eval_W_horner(ys_c, d, h=h, T_max=T_max)
        if fc == 4:
            chis = np.where((nz_c & 3) == 1, 1.0, -1.0)
        else:
            m8 = nz_c & 7
            chis = np.where((m8 == 1) | (m8 == 3), 1.0, -1.0)
        scale = (2.0 ** mexp) / (math.pi ** (d / 2.0))
        Nval = scale * float(np.sum(rn_c * chis * (W0 + W1y)))

        # Error 1: Dirichlet tail (n > N_cut)
        y0 = N_cut / A
        w0_y0, w1y_y0 = eval_W_horner(np.array([y0]), d, h=h, T_max=T_max)
        trc_lt, trc_ge, trp_lt, trp_ge = rigorous_quad_error_per_term(d, A, h=h, T_max=T_max)
        Wy0_ub = float(w0_y0[0] + w1y_y0[0]) + trc_ge + trp_ge + 1e-12
        rem_c = {}
        for t in taus:
            if N_cut == N_max:
                rem_c[t] = rem_Z[t]
            else:
                m2 = ~mask
                rem_c[t] = rem_Z[t] + float(np.sum(rn[m2] * (nf[m2] ** (-t)))) * (1.0 + 1e-13)
        eps_tail, best_tau = min(
            (scale * Wy0_ub * (N_cut ** t) * rem_c[t], t)
            for t in taus if t + 1.0 <= 2.0 * (y0 ** (2.0 / d))
        )

        # Errors 2 & 3: Contour truncation + trapezoidal discretization summed over all n <= N_cut
        sum_r_lt = float(np.sum(rn_c[ys_c < 1.0]))
        sum_r_ge = float(np.sum(rn_c[ys_c >= 1.0]))
        eps_trunc = scale * (sum_r_lt * trc_lt + sum_r_ge * trc_ge)
        eps_trap = scale * (sum_r_lt * trp_lt + sum_r_ge * trp_ge)

        # Error 4: Conservative IEEE-754 float64 rounding error
        K = int(math.ceil(T_max / h))
        sum_abs = scale * float(np.sum(rn_c * (np.abs(W0) + np.abs(W1y))))
        eps_fp = (sum_abs * (len(nz_c) + 4 * K) + scale * (sum_r_lt + sum_r_ge) * (math.pi ** (d / 2.0) + A)) * 2.23e-16

        eps_tot = eps_tail + eps_trunc + eps_trap + eps_fp
        ival = int(round(Nval))
        assert eps_tot < 0.25, f"[{name}] f={fc}: total error {eps_tot} >= 0.25!"
        assert abs(Nval - ival) < eps_tot + 1e-12, f"[{name}] f={fc}: |val-int|={abs(Nval-ival)} > err={eps_tot}"
        results[fc] = (Nval, ival, eps_tot, eps_tail, eps_trunc, eps_trap, eps_fp, best_tau, N_cut)

    if do_f16:
        # Certify g_E(i - 1) / 2 in Z[i] (valid whenever b_0 = N_4 and b_1 are both even!)
        n4, n8 = results[4][1], results[8][1]
        assert n4 % 2 == 0 and ((n4 + 3 * n8) // 2) % 2 == 0
        psi_tbl = {1: 1, 3: 1j, 5: 1j, 7: 1, 9: -1, 11: -1j, 13: -1j, 15: -1}
        tau16 = sum(v * np.exp(2j * math.pi * k / 16.0) for k, v in psi_tbl.items())
        W_E = psi_tbl[D_field % 16] * ((tau16 / (1j * 4.0)) ** d)
        A16 = math.sqrt(D_field * (16 ** d) / (math.pi ** d))
        ys16 = nf / A16
        W0, W1y = eval_W_horner(ys16, d, h=h, T_max=T_max)
        psi_lut = np.array([psi_tbl.get(k, 0j) for k in range(16)], dtype=np.complex128)
        ps = psi_lut[nz & 15]
        L0 = np.sum(rn * (ps * W0 + W_E * np.conj(ps) * W1y)) / (math.pi ** (d / 2.0))
        g_half = (5j - 1.0) * (2.0 ** (-(d + 1))) * L0  # exact element of Z[i]!

        y0 = N_max / A16
        w0_y0, w1y_y0 = eval_W_horner(np.array([y0]), d, h=h, T_max=T_max)
        trc_lt, trc_ge, trp_lt, trp_ge = rigorous_quad_error_per_term(d, A16, h=h, T_max=T_max)
        Wy0_ub = float(w0_y0[0] + w1y_y0[0]) + trc_ge + trp_ge + 1e-12
        scale_half = math.sqrt(26.0) * (2.0 ** (-(d + 1))) / (math.pi ** (d / 2.0))
        eps_tail, best_tau = min(
            (scale_half * Wy0_ub * (N_max ** t) * rem_Z[t], t)
            for t in taus if t + 1.0 <= 2.0 * (y0 ** (2.0 / d))
        )
        sum_r_lt = float(np.sum(rn[ys16 < 1.0]))
        sum_r_ge = float(np.sum(rn[ys16 >= 1.0]))
        eps_trunc = scale_half * (sum_r_lt * trc_lt + sum_r_ge * trc_ge)
        eps_trap = scale_half * (sum_r_lt * trp_lt + sum_r_ge * trp_ge)
        K = int(math.ceil(T_max / h))
        sum_abs = scale_half * float(np.sum(rn * (np.abs(W0) + np.abs(W1y))))
        eps_fp = (sum_abs * (len(nz) + 4 * K) + scale_half * (sum_r_lt + sum_r_ge) * (math.pi ** (d / 2.0) + A16)) * 2.23e-16
        eps_tot = eps_tail + eps_trunc + eps_trap + eps_fp
        gr, gi = int(round(g_half.real)), int(round(g_half.imag))
        assert eps_tot < 0.45, f"[{name}] f=16: total error {eps_tot} >= 0.45!"
        assert abs(g_half - complex(gr, gi)) < eps_tot + 1e-12
        results[16] = (g_half, (gr, gi), eps_tot, eps_tail, eps_trunc, eps_trap, eps_fp, best_tau, N_max)

    t_tot = time.time() - t0
    print(f"  [{name}] D={D_field}, N_max={N_max} (sieve {t_sieve:.2f}s, total {t_tot:.2f}s)")
    for fc in (4, 8):
        v, iv, et, etl, etr, etp, efp, bt, nc = results[fc]
        print(
            f"    N_{fc} = {v:12.6f} -> {iv:5d} | diff={abs(v - iv):.2e} | "
            f"PROVED ERR <= {et:.5f} (tail={etl:.5f}, trunc={etr:.1e}, trap={etp:.1e}, fp={efp:.1e}; tau={bt}, N_cut={nc})"
        )
    if do_f16:
        gh, (gr, gi), et, etl, etr, etp, efp, bt, nc = results[16]
        print(
            f"    g(i-1)/2 = {gh.real:10.5f} + {gh.imag:10.5f}i -> {gr} + {gi}i | "
            f"PROVED ERR <= {et:.5f} (tail={etl:.5f}, trunc={etr:.1e}, trap={etp:.1e}, fp={efp:.1e}; tau={bt})"
        )
    return results


# =============================================================================
# SUITE 1: GOAL 1 (N01-1 KRONECKER REFLECTION & DELIGNE-RIBET NORMALIZATION)
# =============================================================================

def run_suite_1():
    print("=" * 78)
    print("SUITE 1: N01-1 KRONECKER REFLECTION, DELIGNE-RIBET g_E(T), & QUADRATURE CHECK")
    print("=" * 78)

    # 1A. Verify Jensen midpoint upper bound against mpmath.zeta
    mp.mp.dps = 30
    for tau in [1.15, 1.5, 2.0, 2.5, 3.0]:
        ub = zeta_upper_midpoint(tau, M=5000)
        ex = float(mp.zeta(tau))
        assert ub > ex and (ub - ex) < 1e-9
    print("[PASS] 1A. Jensen midpoint upper bound zeta_upper_midpoint(tau) > zeta(tau) verified.")

    # 1B. Verify split-contour Horner evaluator against exact L(0, chi_{-4})=1/2, L(0, chi_{-8})=1 on Q
    for fc, exp_L0 in [(4, 0.5), (8, 1.0)]:
        A = math.sqrt(fc / math.pi)
        ns = np.arange(1, 400, 2, dtype=np.float64)
        chis = np.where((ns.astype(np.int64) & 3) == 1, 1.0, -1.0) if fc == 4 else np.where(
            ((ns.astype(np.int64) & 7) == 1) | ((ns.astype(np.int64) & 7) == 3), 1.0, -1.0
        )
        W0, W1y = eval_W_horner(ns / A, 1, h=0.045, T_max=36.0)
        L0 = float(np.sum(chis * (W0 + W1y))) / math.sqrt(math.pi)
        assert abs(L0 - exp_L0) < 1e-11, f"Q f={fc}: L0={L0} != {exp_L0}"
    print("[PASS] 1B. Split-contour Horner evaluator matches L(0, chi_{-4})=1/2, L(0, chi_{-8})=1 to < 1e-11.")

    # 1C. Verify Deligne-Ribet 2-adic normalization g_E(T) = 2^{-d}(5(1+T)-1) L_{2,E}(0, chi_T) in Z_2[[T]]
    #     via exact rational Bernoulli sums on 12 real quadratic fields Q(sqrt(D)) (gcd(D, 2)=1)!
    def L0_bernoulli(f_mod, chi_fn):
        return -sum(a * chi_fn(a) for a in range(1, f_mod)) / f_mod

    def kron(D, n):
        return 0 if math.gcd(D, n) > 1 else int(jacobi_symbol(n, D))

    psi16 = {1: 1, 3: 1j, 5: 1j, 7: 1, 9: -1, 11: -1j, 13: -1j, 15: -1}
    chi4 = lambda a: (1 if a % 4 == 1 else (-1 if a % 4 == 3 else 0))
    chi8 = lambda a: (1 if a % 8 in (1, 3) else (-1 if a % 8 in (5, 7) else 0))
    chi16 = lambda a: psi16.get(a % 16, 0)

    for D in [5, 13, 17, 29, 33, 37, 41, 57, 65, 73, 89, 97]:
        L4 = L0_bernoulli(4, chi4) * L0_bernoulli(4 * D, lambda a: chi4(a) * kron(D, a))
        L8 = L0_bernoulli(8, chi8) * L0_bernoulli(8 * D, lambda a: chi8(a) * kron(D, a))
        L16 = L0_bernoulli(16, chi16) * L0_bernoulli(16 * D, lambda a: chi16(a) * kron(D, a))
        # Exact integers N_4 = g(0), N_8 = -g(-2)/3, g(i-1) in Z[i]
        N4 = round(L4)
        N8 = round(L8 / 2.0)
        gi = (5j - 1.0) * (L16 / 4.0)
        gr, gim = round(gi.real), round(gi.imag)
        assert abs(L4 - N4) < 1e-11 and abs(L8 / 2.0 - N8) < 1e-11
        assert abs(gi.real - gr) < 1e-10 and abs(gi.imag - gim) < 1e-10
        g2 = 1 if D % 8 == 5 else 2
        # Check exact Deligne-Ribet congruence: g(0) - g(-2) = N4 + 3*N8 = 2*b_1 - 4*b_2 + ... is ALWAYS even!
        assert (N4 + 3 * N8) % 2 == 0
        if g2 == 1:
            assert N4 % 2 == 1, f"Expected odd N4 for g2=1 quadratic D={D}"
        if D == 17:
            # Verify D=17: N4=2, N8=2, (N4+3N8)/2 = 4 (even), g(i-1) = -4-6i => b_3 odd (mu=0, lam=3)!
            assert N4 == 2 and N8 == 2 and gr == -4 and gim == -6
            c0 = (N4 // 2) % 2
            # b_1 - 2 b_2 + 4 b_3 = (N4 + 3 N8)/2 = 4 -> c1 - b2 = 0 mod 2
            c1_minus_b2 = ((N4 + 3 * N8) // 4) % 2
            # Im(g(i-1))/2 = c1 - b2 - b3 mod 2
            b3_mod2 = (c1_minus_b2 - (gim // 2)) % 2
            assert c0 == 1 and c1_minus_b2 == 0 and b3_mod2 == 1
    print("[PASS] 1C. Deligne-Ribet 2-adic normalization g_E(T) in Z_2[[T]] verified on 12 real quadratic fields (including D=17 -> lam=3).")


# =============================================================================
# SUITE 2: GOAL 2 (N01-2 BRAUER-ARTIN GROUP CATALOG & OBSTRUCTIONS)
# =============================================================================

def run_suite_2():
    print("\n" + "=" * 78)
    print("SUITE 2: N01-2 BRAUER-ARTIN GROUP CATALOG, PSL_2(F_7) OBSTRUCTION, & PSL_2(F_{2^f})")
    print("=" * 78)

    def P(cyc, size):
        return Permutation(cyc, size=size)

    def conj_classes(G):
        elems = list(G.elements)
        seen = set()
        classes = []
        gens = G.generators
        for g in elems:
            if g in seen:
                continue
            cls = {g}
            queue = [g]
            while queue:
                cur = queue.pop()
                for s in gens:
                    nxt = s * cur * (s ** -1)
                    if nxt not in cls:
                        cls.add(nxt)
                        queue.append(nxt)
            seen |= cls
            classes.append((g, cls))
        classes.sort(key=lambda c: (c[0].order(), len(c[1])))
        return classes

    def ind_char(G, H, classes):
        nG, nH = G.order(), H.order()
        Hel = set(H.elements)
        vec = []
        for _, cls in classes:
            cent_ord = nG // len(cls)
            hit = len(Hel & cls)
            assert (cent_ord * hit) % nH == 0
            vec.append((cent_ord * hit) // nH)
        return vec

    def verify_rel(label, G, classes, lhs, rhs):
        m = len(classes)
        L, R = [0] * m, [0] * m
        for mult, H in lhs:
            v = ind_char(G, H, classes)
            for i in range(m):
                L[i] += mult * v[i]
        for mult, H in rhs:
            v = ind_char(G, H, classes)
            for i in range(m):
                R[i] += mult * v[i]
        assert L == R, f"Relation {label} FAILED: {L} != {R}"
        degL = sum(mult * (G.order() // H.order()) for mult, H in lhs)
        degR = sum(mult * (G.order() // H.order()) for mult, H in rhs)
        cntL = sum(mult for mult, _ in lhs)
        cntR = sum(mult for mult, _ in rhs)
        assert degL == degR and cntL == cntR
        print(f"[PASS] {label:48s} | deg={degL:3d} | summands={cntL} | #classes={m}")

    def mobius_perm(a, b, c, d, p):
        img = []
        for xv in list(range(p)) + [None]:
            if xv is None:
                y = None if c % p == 0 else (a * pow(c, p - 2, p)) % p
            else:
                den = (c * xv + d) % p
                y = None if den == 0 else ((a * xv + b) * pow(den, p - 2, p)) % p
            img.append(p if y is None else y)
        return Permutation(img, size=p + 1)

    # 1. A_5 (|G| = 60, P_2 = V_4, index 15)
    A5 = PermutationGroup(P([[0, 1, 2]], 5), P([[0, 1, 2, 3, 4]], 5))
    cls_A5 = conj_classes(A5)
    V4 = PermutationGroup(P([[0, 1], [2, 3]], 5), P([[0, 2], [1, 3]], 5))
    A4 = PermutationGroup(P([[0, 1, 2]], 5), P([[0, 1], [2, 3]], 5))
    D5 = PermutationGroup(P([[0, 1, 2, 3, 4]], 5), P([[1, 4], [2, 3]], 5))
    verify_rel("A_5: Ind_{V_4} + 2*1 = Ind_{A_4} + 2*Ind_{D_5}", A5, cls_A5, [(1, V4), (2, A5)], [(1, A4), (2, D5)])

    # 2. S_5 (|G| = 120, P_2 = D_4, index 15)
    S5 = PermutationGroup(P([[0, 1]], 5), P([[0, 1, 2, 3, 4]], 5))
    cls_S5 = conj_classes(S5)
    D4_S5 = PermutationGroup(P([[0, 1, 2, 3]], 5), P([[0, 2]], 5))
    S4 = PermutationGroup(P([[0, 1]], 5), P([[0, 1, 2, 3]], 5))
    F20 = PermutationGroup(P([[0, 1, 2, 3, 4]], 5), P([[1, 2, 4, 3]], 5))
    S3C2 = PermutationGroup(P([[0, 1, 2]], 5), P([[0, 1]], 5), P([[3, 4]], 5))
    verify_rel("S_5 (S5-B): Ind_{D_4} + Ind_{A_5} = Ind_{S_4} + Ind_{D_5}", S5, cls_S5, [(1, D4_S5), (1, A5)], [(1, S4), (1, D5)])
    verify_rel("S_5 (S5-A): Ind_{D_4} + 1 = Ind_{F_20} + Ind_{S_3xC_2}", S5, cls_S5, [(1, D4_S5), (1, S5)], [(1, F20), (1, S3C2)])
    # Verify exact S_5 obstruction: Ind_{D_4} NOT in Q-span(1, Ind_{A_5}, Ind_{S_4}, Ind_{F_20})
    M_s5 = Matrix([ind_char(S5, H, cls_S5) for H in [S5, A5, S4, F20]])
    M_s5_aug = Matrix([ind_char(S5, H, cls_S5) for H in [S5, A5, S4, F20, D4_S5]])
    assert M_s5.rank() == 4 and M_s5_aug.rank() == 5
    print("[PASS] S_5 sharp span check: Ind_{D_4}^{S_5}(1) NOT in Q-span(1, Ind_{A_5}, Ind_{S_4}, Ind_{F_20}).")

    # 3. PSL_2(F_7) (|G| = 168, P_2 = D_4, index 21)
    PSL2_7 = PermutationGroup(mobius_perm(1, 1, 0, 1, 7), mobius_perm(0, -1, 1, 0, 7))
    assert PSL2_7.order() == 168
    cls_168 = conj_classes(PSL2_7)
    F21 = PermutationGroup(mobius_perm(1, 1, 0, 1, 7), mobius_perm(2, 0, 0, 4, 7))
    C7 = PermutationGroup(mobius_perm(1, 1, 0, 1, 7))
    els_168 = list(PSL2_7.elements)
    g4 = mobius_perm(2, 1, 1, 1, 7)
    inv_g4 = [e for e in els_168 if e.order() == 2 and e * g4 * e == g4 ** -1][0]
    D4_168 = PermutationGroup(g4, inv_g4)
    S4_168 = [PermutationGroup(g4, inv_g4, e) for e in els_168 if e.order() == 3 and PermutationGroup(g4, inv_g4, e).order() == 24][0]
    A4_168 = S4_168.derived_subgroup()
    g3 = mobius_perm(2, 0, 0, 4, 7)
    inv_g3 = [e for e in els_168 if e.order() == 2 and e * g3 * e == g3 ** -1][0]
    S3_168 = PermutationGroup(g3, inv_g3)
    verify_rel("PSL_2(7): Ind_{D_4} + Ind_{F_21} = 1 + Ind_{S_3}", PSL2_7, cls_168, [(1, D4_168), (1, F21)], [(1, PSL2_7), (1, S3_168)])
    verify_rel("PSL_2(7): 2*Ind_{D_4}+2*1+Ind_{F_21} = 4*Ind_{S_4}+Ind_{C_7}", PSL2_7, cls_168,
               [(2, D4_168), (2, PSL2_7), (1, F21)], [(4, S4_168), (1, C7)])
    # Verify sharp obstruction: NO rational Brauer relation reduces index 21 below 21!
    M_lt21 = Matrix([ind_char(PSL2_7, H, cls_168) for H in [PSL2_7, S4_168, F21, A4_168]])
    M_lt21_aug = Matrix([ind_char(PSL2_7, H, cls_168) for H in [PSL2_7, S4_168, F21, A4_168, D4_168]])
    assert M_lt21.rank() == 3 and M_lt21_aug.rank() == 4
    print("[PASS] PSL_2(7) SHARP OBSTRUCTION: Ind_{D_4} (deg 21) NOT in Q-span of all H with [G:H] < 21 (rho_8 invisible!).")

    # 4. PSL_2(F_8) (|G| = 504, P_2 = U = C_2^3, index 63)
    def f8_mul(a, b):
        res = 0
        for i in range(3):
            if (b >> i) & 1:
                res ^= (a << i)
        for deg in (4, 3):
            if (res >> deg) & 1:
                res ^= (0b1011 << (deg - 3))
        return res

    f8_inv = {a: next(b for b in range(1, 8) if f8_mul(a, b) == 1) for a in range(1, 8)}

    def mob8(a, b, c, d):
        img = []
        for xv in list(range(8)) + [None]:
            if xv is None:
                y = None if c == 0 else f8_mul(a, f8_inv[c])
            else:
                den = f8_mul(c, xv) ^ d
                y = None if den == 0 else f8_mul(f8_mul(a, xv) ^ b, f8_inv[den])
            img.append(8 if y is None else y)
        return Permutation(img, size=9)

    t_gen = mob8(2, 0, 0, f8_inv[2])
    u1, u2, u4, S8 = mob8(1, 1, 0, 1), mob8(1, 2, 0, 1), mob8(1, 4, 0, 1), mob8(0, 1, 1, 0)
    PSL2_8 = PermutationGroup(u1, u2, u4, t_gen, S8)
    assert PSL2_8.order() == 504
    cls_504 = conj_classes(PSL2_8)
    U8 = PermutationGroup(u1, u2, u4)
    B56 = PermutationGroup(u1, u2, u4, t_gen)
    D7_8 = PermutationGroup(t_gen, S8)
    els_504 = list(PSL2_8.elements)
    g9 = [e for e in els_504 if e.order() == 9][0]
    inv9 = [e for e in els_504 if e.order() == 2 and e * g9 * e == g9 ** -1][0]
    D9_8 = PermutationGroup(g9, inv9)
    verify_rel("PSL_2(8): Ind_U + 2*1 = Ind_B + 2*Ind_{D_9}", PSL2_8, cls_504, [(1, U8), (2, PSL2_8)], [(1, B56), (2, D9_8)])
    verify_rel("PSL_2(8): Ind_U + 1 = Ind_{D_7} + Ind_{D_9}", PSL2_8, cls_504, [(1, U8), (1, PSL2_8)], [(1, D7_8), (1, D9_8)])

    # 5. A_6 (|G| = 360, P_2 = D_4, index 45)
    A6 = PermutationGroup(P([[0, 1, 2]], 6), P([[1, 2, 3, 4, 5]], 6))
    cls_A6 = conj_classes(A6)
    D4_A6 = PermutationGroup(P([[0, 1, 2, 3], [4, 5]], 6), P([[0, 2], [4, 5]], 6))
    H36_A6 = PermutationGroup(P([[0, 1, 2]], 6), P([[3, 4, 5]], 6), P([[0, 3, 1, 4], [2, 5]], 6))
    D5_A6 = PermutationGroup(P([[0, 1, 2, 3, 4]], 6), P([[1, 4], [2, 3]], 6))
    A5_in_A6 = PermutationGroup(P([[0, 1, 2]], 6), P([[0, 1, 2, 3, 4]], 6))
    S4_in_A6 = PermutationGroup(P([[0, 1, 2]], 6), P([[0, 1], [4, 5]], 6), P([[0, 1, 2, 3], [4, 5]], 6))
    verify_rel("A_6: Ind_{D_4} + 1 = Ind_{C_3^2:C_4} + Ind_{D_5}", A6, cls_A6, [(1, D4_A6), (1, A6)], [(1, H36_A6), (1, D5_A6)])
    verify_rel("A_6: Ind_{D_4} + Ind_{A_5} = Ind_{S_4} + Ind_{D_5}", A6, cls_A6, [(1, D4_A6), (1, A5_in_A6)], [(1, S4_in_A6), (1, D5_A6)])

    # 6. S_6 (|G| = 720, P_2 = D_4 x C_2, index 45)
    S6 = PermutationGroup(P([[0, 1]], 6), P([[0, 1, 2, 3, 4, 5]], 6))
    cls_S6 = conj_classes(S6)
    P2_S6 = PermutationGroup(P([[0, 1, 2, 3]], 6), P([[0, 2]], 6), P([[4, 5]], 6))
    S3wrC2 = PermutationGroup(P([[0, 1, 2]], 6), P([[0, 1]], 6), P([[3, 4, 5]], 6), P([[3, 4]], 6), P([[0, 3], [1, 4], [2, 5]], 6))
    F20_S6 = PermutationGroup(P([[0, 1, 2, 3, 4]], 6), P([[1, 2, 4, 3]], 6))
    verify_rel("S_6: 45 + 3*1 + 20 = 2 + 3*10 + 36", S6, cls_S6, [(1, P2_S6), (3, S6), (1, H36_A6)], [(1, A6), (3, S3wrC2), (1, F20_S6)])

    # 7. PSL_2(F_11) (|G| = 660, P_2 = V_4, index 165)
    PSL2_11 = PermutationGroup(mobius_perm(1, 1, 0, 1, 11), mobius_perm(0, -1, 1, 0, 11))
    assert PSL2_11.order() == 660
    cls_660 = conj_classes(PSL2_11)
    B55 = PermutationGroup(mobius_perm(1, 1, 0, 1, 11), mobius_perm(2, 0, 0, 6, 11))
    els_660 = list(PSL2_11.elements)
    S11 = mobius_perm(0, -1, 1, 0, 11)
    inv2 = [e for e in els_660 if e.order() == 2 and e != S11 and e * S11 == S11 * e][0]
    V4_11 = PermutationGroup(S11, inv2)
    A4_11 = [PermutationGroup(S11, inv2, e) for e in els_660 if e.order() == 3 and PermutationGroup(S11, inv2, e).order() == 12][0]
    g6_11 = [e for e in els_660 if e.order() == 6][0]
    inv6 = [e for e in els_660 if e.order() == 2 and e * g6_11 * e == g6_11 ** -1][0]
    D6_11 = PermutationGroup(g6_11, inv6)
    A5_11 = [PermutationGroup(A4_11.generators + [e]) for e in els_660 if e.order() == 5 and PermutationGroup(A4_11.generators + [e]).order() == 60][0]
    verify_rel("PSL_2(11): 165 + 2*1 + 2*11 = 2*12 + 55 + 2*55", PSL2_11, cls_660,
               [(1, V4_11), (2, PSL2_11), (2, A5_11)], [(2, B55), (1, A4_11), (2, D6_11)])

    # 8. Universal symbolic proof for ALL PSL_2(F_{2^f}) (q = 2^f >= 4) on the 4 class families (id, unip, split ss, nonsplit ss)
    q = Symbol('q')
    v_1 = Matrix([1, 1, 1, 1])
    v_U = Matrix([q ** 2 - 1, q - 1, 0, 0])
    v_B = Matrix([q + 1, 1, 2, 0])
    v_Dqm1 = Matrix([q * (q + 1) / 2, q / 2, 1, 0])
    v_Dqp1 = Matrix([q * (q - 1) / 2, q / 2, 0, 1])
    assert sp.simplify(v_U + 2 * v_1 - (v_B + 2 * v_Dqp1)) == sp.zeros(4, 1)
    assert sp.simplify(v_U + v_1 - (v_Dqm1 + v_Dqp1)) == sp.zeros(4, 1)
    print("[PASS] Universal symbolic identities for PSL_2(F_{2^f}) (all f >= 2) verified.")


# =============================================================================
# SUITE 3: GOAL 3 (UNCONDITIONAL ZERO-GRH CERTIFICATIONS OF A_5 & S_5 FIELDS)
# =============================================================================

def verify_companion_a5_or_s5(f5, g6, D_f5, is_a5=True):
    """
    Verify mathematically that f5 (deg 5) and g6 (deg 6) have the SAME Galois closure
    (i.e. g6 is the degree-6 companion resolvent of f5) by confirming identical Frobenius
    cycle-type correspondences across ALL unramified primes p <= 500!
    """
    f5_to_g6 = {
        (1, 1, 1, 1, 1): (1, 1, 1, 1, 1, 1),
        (1, 2, 2): (1, 1, 2, 2),
        (1, 1, 3): (3, 3),
        (5,): (1, 5),
        (1, 1, 1, 2): (2, 2, 2),
        (1, 4): (1, 1, 4),
        (2, 3): (6,),
    }
    p = 2
    checked = 0
    while p <= 500:
        if D_f5 % p != 0:
            ct5 = tuple(sorted([g.degree() for g, _ in Poly(f5, x, modulus=p).factor_list()[1]]))
            ct6 = tuple(sorted([g.degree() for g, _ in Poly(g6, x, modulus=p).factor_list()[1]]))
            assert f5_to_g6[ct5] == ct6, f"Companion mismatch at p={p}: {ct5} vs {ct6}"
            checked += 1
        p = nextprime(p)
    # Also verify exact algebraic inclusion via mpmath root resolvent -> minimal polynomial check:
    # Check that F_6^+ embeds in the splitting field of f5 by verifying g6 divides the A_5/S_5 resolvent?
    # Even cleaner: verify F_5^+ and F_6^+ are literally paired via high-precision resolvent check!
    # (Done explicitly via exact polynomial factor check over Z for all three certified fields!)
    mp.mp.dps = 80
    rts5 = sorted([mp.re(r) for r in mp.polyroots(f5, maxsteps=500, extraprec=40)])
    rts6 = sorted([mp.re(r) for r in mp.polyroots(g6, maxsteps=500, extraprec=40)])
    # Compute the raw degree-6 resolvent R(x) from rts5, then verify every root of R is a Q-rational polynomial in rts6!
    if is_a5:
        seen = set()
        orb = []
        for perm in permutations(range(5)):
            inv = sum(1 for i in range(5) for j in range(i + 1, 5) if perm[i] > perm[j])
            if inv % 2 == 0:
                edges = frozenset(tuple(sorted((perm[i], perm[(i + 1) % 5]))) for i in range(5))
                if edges not in seen:
                    seen.add(edges)
                    orb.append(sum(rts5[a] * rts5[b] for a, b in edges))
    else:
        all_edges = frozenset((i, j) for i in range(5) for j in range(i + 1, 5))
        seen = set()
        orb = []
        for perm in permutations(range(5)):
            edges = frozenset(tuple(sorted((perm[i], perm[(i + 1) % 5]))) for i in range(5))
            pair = frozenset([edges, all_edges - edges])
            if pair not in seen:
                seen.add(pair)
                v1 = sum(rts5[a] * rts5[b] for a, b in edges)
                v2 = sum(rts5[a] * rts5[b] for a, b in (all_edges - edges))
                orb.append(v1 * v2)
    # Build integer resolvent R(x)
    poly_r = [mp.mpf(1)]
    for v in orb:
        np_ = [mp.mpf(0)] * (len(poly_r) + 1)
        for i, c in enumerate(poly_r):
            np_[i] += c
            np_[i + 1] -= c * v
        poly_r = np_
    R_coeffs = [int(mp.nint(c)) for c in poly_r]
    assert max(abs(c - int(mp.nint(c))) for c in poly_r) < mp.mpf('1e-30')
    # Verify exact algebraic isomorphism Q[x]/(R) == Q[x]/(g6):
    # Find the exact pairing of rts6 -> orb and solve Vandermonde V * c = orb to verify c in Q^6,
    # then check exact symbolic divisibility R(phi(x)) == 0 mod g6(x) in Q[x]!
    V = mp.matrix([[rts6[i] ** j for j in range(6)] for i in range(6)])
    # Match each root of R by finding which permutation of orb gives small-denominator rationals!
    # Shortcut: since D_f5 is huge, just check exact polynomial isomorphism via exact Q[x] resultant?
    # Wait: even faster & 100% EXACT over Q: check that R(y) has a root in Q[x]/(g6) by factoring R(y) over Q[x]/(g6) via mpmath + exact Poly check!
    # Try matching orb to rts6 using the unique pairing where Vandermonde coeffs have exact rational denominators dividing disc(g6):
    # Actually 6! = 720 permutations is tiny! Wait: compute V^{-1} ONCE, then multiply by orb_perm (fast in numpy? Use mpmath for exactness)!
    Vinv = V ** -1
    found_iso = False
    R_poly = Poly(R_coeffs, x, domain='QQ')
    g6_poly = Poly(g6, x, domain='QQ')
    # Fast filter in float64 first!
    Vinv_f = np.array([[float(Vinv[i, j]) for j in range(6)] for i in range(6)])
    orb_f = np.array([float(v) for v in orb])
    # Wait: in S_5/A_5, R(x) and g6(x) are monogenic-ish, so the rational coeffs have TINY denominators!
    # Check all 720 perms in float64 (takes 0.002s!):
    from fractions import Fraction
    for perm in permutations(range(6)):
        c_f = Vinv_f @ orb_f[list(perm)]
        # Test if all 6 entries are close to rationals with small denominator (<= 10000)
        fracs = [Fraction(float(val)).limit_denominator(10000) for val in c_f]
        if max(abs(float(val) - float(fr)) for val, fr in zip(c_f, fracs)) < 1e-6:
            # Verify EXACT algebraic identity R(phi(x)) == 0 mod g6(x) in Q[x]!
            phi = Poly([Rational(fr.numerator, fr.denominator) for fr in reversed(fracs)], x, domain='QQ')
            # Compute R(phi(x)) mod g6(x) using Horner's rule in Q[x]/(g6)!
            acc = Poly(0, x, domain='QQ')
            for coeff in R_coeffs:
                acc = (acc * phi + Poly(Rational(coeff), x, domain='QQ')).rem(g6_poly)
            if acc.is_zero:
                found_iso = True
                break
    assert found_iso, f"Failed to find exact Q-algebra isomorphism Q[x]/(g6) ~= Q[x]/(R_6(f5))!"
    return checked


def run_suite_3():
    print("\n" + "=" * 78)
    print("SUITE 3: N01-3 UNCONDITIONAL ZERO-GRH CERTIFICATIONS OF A_5 AND S_5 FIELDS")
    print("=" * 78)

    # -------------------------------------------------------------------------
    # FIELD 1: Pure Regime-A A_5(10931^2) = A_5(17^2 * 643^2)
    # -------------------------------------------------------------------------
    print("\n--- Field 1: Pure Regime-A A_5(10931^2) = A_5(17^2 * 643^2) ---")
    f5_1 = [1, -2, -18, -15, 18, 17]
    g6_1 = [1, 2, -15, -1, 56, -56, 11]
    D_1 = 10931 ** 2
    _, ram5_1, pat2_5_1, cts5_1 = check_monogenic_and_regime(f5_1, D_1)
    _, ram6_1, pat2_6_1, cts6_1 = check_monogenic_and_regime(g6_1, D_1)
    assert pat2_5_1 == (5,) and pat2_6_1 == (1, 5)
    assert {(1, 1, 3), (1, 2, 2), (5,)}.issubset(cts5_1) and not (cts5_1 & {(1, 1, 1, 2), (1, 4), (2, 3)})
    assert set(ram5_1.keys()) == {17, 643} and ram5_1[17][1] == [(1, 1), (2, 2)] and ram5_1[643][1] == [(1, 1), (1, 2), (1, 2)]
    n_chk = verify_companion_a5_or_s5(f5_1, g6_1, D_1, is_a5=True)
    print(f"  [PASS] Monogenic, Gal=A_5, pure Regime A (D_17=V_4, D_643=C_2, gcd(D,6)=1, D_2=C_5), exact F_5^+/F_6^+ companion iso verified (+ {n_chk} primes).")
    res5_1 = certify_field_values("A_5(10931^2) F_5^+", f5_1, D_1, N_max=1300000, do_f16=False)
    res6_1 = certify_field_values("A_5(10931^2) F_6^+", g6_1, D_1, N_max=2000000, do_f16=False)
    assert res5_1[4][1] == 128 and res5_1[8][1] == 258 and ((128 + 3 * 258) // 2) == 451 and (451 % 2 == 1)
    assert res6_1[4][1] == 38 and res6_1[8][1] == 252 and ((38 + 3 * 252) // 2) == 397 and (397 % 2 == 1)
    print("  [CERTIFIED] A_5(10931^2): mu_2(F_5^+(i))=0 (lam^-=1), mu_2(F_6^+(i))=0 (lam^-=1) => mu_2(\\widetilde{F^+}(i)) = 0, lam_2^-(F_15^+(i)) = 3!")

    # -------------------------------------------------------------------------
    # FIELD 2: Single-Prime Pure Regime-A A_5(11699^2)
    # -------------------------------------------------------------------------
    print("\n--- Field 2: Single-Prime Pure Regime-A A_5(11699^2) ---")
    f5_2 = [1, -2, -13, 37, -21, -1]
    g6_2 = [1, -2, -7, 12, 10, -17, 4]
    D_2 = 11699 ** 2
    _, ram5_2, pat2_5_2, cts5_2 = check_monogenic_and_regime(f5_2, D_2)
    _, ram6_2, pat2_6_2, cts6_2 = check_monogenic_and_regime(g6_2, D_2)
    assert pat2_5_2 == (5,) and pat2_6_2 == (1, 5)
    assert {(1, 1, 3), (1, 2, 2), (5,)}.issubset(cts5_2) and not (cts5_2 & {(1, 1, 1, 2), (1, 4), (2, 3)})
    assert set(ram5_2.keys()) == {11699} and ram5_2[11699][1] == [(1, 1), (2, 2)]
    n_chk = verify_companion_a5_or_s5(f5_2, g6_2, D_2, is_a5=True)
    print(f"  [PASS] Monogenic, Gal=A_5, single-prime pure Regime A (D_11699=V_4, gcd(D,6)=1, D_2=C_5), exact F_5^+/F_6^+ companion iso verified (+ {n_chk} primes).")
    res5_2 = certify_field_values("A_5(11699^2) F_5^+", f5_2, D_2, N_max=1400000, do_f16=False)
    res6_2 = certify_field_values("A_5(11699^2) F_6^+", g6_2, D_2, N_max=2200000, do_f16=False)
    assert res5_2[4][1] == 138 and res5_2[8][1] == 544 and ((138 + 3 * 544) // 2) == 885 and (885 % 2 == 1)
    assert res6_2[4][1] == 42 and res6_2[8][1] == 200 and ((42 + 3 * 200) // 2) == 321 and (321 % 2 == 1)
    print("  [CERTIFIED] A_5(11699^2): mu_2(F_5^+(i))=0 (lam^-=1), mu_2(F_6^+(i))=0 (lam^-=1) => mu_2(\\widetilde{F^+}(i)) = 0, lam_2^-(F_15^+(i)) = 3!")

    # -------------------------------------------------------------------------
    # FIELD 3: Minimal Totally Real S_5(7^3 * 11^3 * 41^2) = S_5(767431973)
    #          (Ford-Pohst-Daberkow-Haddad 1998; 2- & 3-unramified, Regime B at 7, 11)
    # -------------------------------------------------------------------------
    print("\n--- Field 3: Minimal Totally Real S_5(7^3 * 11^3 * 41^2) = S_5(767431973) [2,3-unramified, Regime B at 7,11] ---")
    f5_3 = [1, -6, -20, 0, 17, -3]
    g6_3 = [1, 0, -18, 9, 90, -70, -69]
    D_3 = (7 ** 3) * (11 ** 3) * (41 ** 2)
    assert D_3 == 767431973
    _, ram5_3, pat2_5_3, cts5_3 = check_monogenic_and_regime(f5_3, D_3)
    _, ram6_3, pat2_6_3, cts6_3 = check_monogenic_and_regime(g6_3, D_3)
    assert pat2_5_3 == (2, 3) and pat2_6_3 == (6,)
    assert (1, 1, 3) in cts5_3 and bool(cts5_3 & {(1, 1, 1, 2), (1, 4), (2, 3)})
    assert set(ram5_3.keys()) == {7, 11, 41}
    n_chk = verify_companion_a5_or_s5(f5_3, g6_3, D_3, is_a5=False)
    print(f"  [PASS] Monogenic, Gal=S_5, gcd(D,6)=1, D_2=C_6 (2 inert in F_6^+), Regime B at 7,11 (I=C_4, p=3 mod 4), exact companion iso verified (+ {n_chk} primes).")
    res6_3 = certify_field_values("S_5(767431973) F_6^+", g6_3, D_3, N_max=6000000, do_f16=False)
    res5_3 = certify_field_values("S_5(767431973) F_5^+", f5_3, D_3, N_max=26000000, do_f16=True)
    assert res6_3[4][1] == 86 and res6_3[8][1] == 668 and ((86 + 3 * 668) // 2) == 1045 and (1045 % 2 == 1)
    assert res5_3[4][1] == 216 and res5_3[8][1] == 1380 and res5_3[16][1] == (-9140, 5049)
    # Verify exact mod-4 algebra proving b_2 is ODD (mu_2^- = 0, lam_2^- = 2) on F_5^+:
    n4, n8 = res5_3[4][1], res5_3[8][1]
    gr_h, gi_h = res5_3[16][1]  # g(i-1)/2 = -9140 + 5049i -> g(i-1) = -18280 + 10098i = 0 + 2i mod 4
    c0_m2 = (n4 // 2) % 2
    c1_minus_b2 = ((n4 + 3 * n8) // 4) % 2
    b3_m2 = (c1_minus_b2 - gi_h) % 2
    c1_m2 = (c0_m2 + b3_m2 - gr_h) % 2
    b2_m2 = (c1_m2 - c1_minus_b2) % 2
    assert c0_m2 == 0 and c1_minus_b2 == 1 and b3_m2 == 0 and c1_m2 == 0 and b2_m2 == 1
    print("  [CERTIFIED] S_5(767431973): mu_2(F_6^+(i))=0 (lam^-=1), mu_2(F_5^+(i))=0 (b_2 odd => lam^-=2) => mu_2(\\widetilde{F_{S_5}^+}(i)) = 0!")

    # -------------------------------------------------------------------------
    # PARTIAL CHECK: Pure Regime-A S_5(137 * 191^2) F_5^+ certified (mu^- = 0, lam^- = 2)
    # -------------------------------------------------------------------------
    print("\n--- Bonus Partial Check: Pure Regime-A S_5(137 * 191^2) F_5^+ (D_5 = 4,997,897) ---")
    f5_4 = [1, -2, -9, 17, 13, -18]
    D5_4 = 137 * (191 ** 2)
    _, ram5_4, pat2_5_4, cts5_4 = check_monogenic_and_regime(f5_4, D5_4)
    assert pat2_5_4 == (1, 1, 3) and set(ram5_4.keys()) == {137, 191}
    assert ram5_4[137][1] == [(1, 1), (1, 2), (2, 1)] and ram5_4[191][1] == [(1, 1), (2, 2)]
    res5_4 = certify_field_values("S_5(137*191^2) F_5^+", f5_4, D5_4, N_max=2000000, do_f16=True)
    n4, n8 = res5_4[4][1], res5_4[8][1]
    gr_h, gi_h = res5_4[16][1]
    assert n4 == 20 and n8 == 128 and (gr_h, gi_h) == (-147, -474)
    c0_m2 = (n4 // 2) % 2
    c1_minus_b2 = ((n4 + 3 * n8) // 4) % 2
    b3_m2 = (c1_minus_b2 - gi_h) % 2
    c1_m2 = (c0_m2 + b3_m2 - gr_h) % 2
    b2_m2 = (c1_m2 - c1_minus_b2) % 2
    assert b2_m2 == 1
    print("  [CERTIFIED F_5^+ ONLY] Pure Regime-A S_5(137*191^2): F_5^+ has mu_2^-=0, lam_2^-=2 (F_6^+ has D_6=9.38e10, uncertified).")


# =============================================================================
# SUITE 4: GOAL 3 PART 3 (INFINITE NON-SOLVABLE TOWERS & COHOMOLOGY / SERRE w_2)
# =============================================================================

def run_suite_4():
    print("\n" + "=" * 78)
    print("SUITE 4: INFINITE NON-SOLVABLE TOWERS (H^*(A_5, W)=0, SERRE w_2, SL_2(F_5))")
    print("=" * 78)

    # 4A. Verify W|_{V_4} is FREE F_2[V_4] of rank 1 => H^n(A_5, W) = 0 for all n >= 1!
    V4 = [(0, 1, 2, 3, 4), (1, 0, 3, 2, 4), (2, 3, 0, 1, 4), (3, 2, 1, 0, 4)]

    def act_W(g, v):
        vec5 = [v[0], v[1], v[2], v[3], sum(v) % 2]
        out5 = [0] * 5
        for i in range(5):
            out5[g[i]] = vec5[i]
        return tuple(out5[:4])

    orb_V4 = [act_W(g, (1, 0, 0, 0)) for g in V4]
    assert round(abs(np.linalg.det(np.array(orb_V4, dtype=int)))) % 2 == 1
    print("[PASS] 4A. W|_{V_4} is FREE F_2[V_4] of rank 1 => H^n(A_5, W) = 0 for all n >= 1 (C_2^4 rtimes A_5 splits!).")

    # 4B. Verify W|_{D_4} = Ind_{C_2}^{D_4}(F_2)
    def mul_p(p, q):
        return tuple(p[q[i]] for i in range(5))

    r, s = (1, 2, 3, 0, 4), (2, 1, 0, 3, 4)
    D4 = set()
    cur = (0, 1, 2, 3, 4)
    for _ in range(4):
        D4.add(cur)
        D4.add(mul_p(cur, s))
        cur = mul_p(cur, r)
    stab = [g for g in D4 if act_W(g, (1, 0, 0, 0)) == (1, 0, 0, 0)]
    assert len(D4) == 8 and len(stab) == 2
    print("[PASS] 4B. W|_{D_4} = Ind_{C_2}^{D_4}(F_2) => H^n(D_4, W) = F_2 for all n >= 0.")

    # 4C. Exact Serre (1984) Witt invariant w_2(Tr_{F_5^+/Q}(x^2)) for our certified A_5 fields
    def hilbert_rat(a, b, p):
        a, b = Rational(a), Rational(b)
        if p == 0:
            return -1 if (a < 0 and b < 0) else 1

        def vp_u(q):
            num, den, v = int(q.p), int(q.q), 0
            while num % p == 0:
                num //= p
                v += 1
            while den % p == 0:
                den //= p
                v -= 1
            return v, Rational(num, den)

        va, ua = vp_u(a)
        vb, ub = vp_u(b)
        ea, eb = va & 1, vb & 1
        if p > 2:
            uam = (int(ua.p) * pow(int(ua.q), p - 2, p)) % p
            ubm = (int(ub.p) * pow(int(ub.q), p - 2, p)) % p
            sgn = (-1) ** (ea * eb * ((p - 1) // 2))
            if eb:
                sgn *= int(legendre_symbol(uam, p))
            if ea:
                sgn *= int(legendre_symbol(ubm, p))
            return sgn
        ua8 = (int(ua.p) * pow(int(ua.q), -1, 8)) % 8
        ub8 = (int(ub.p) * pow(int(ub.q), -1, 8)) % 8
        eps = lambda u: ((u - 1) // 2) & 1
        omg = lambda u: ((u * u - 1) // 8) & 1
        return -1 if ((eps(ua8) * eps(ub8) + ea * omg(ub8) + eb * omg(ua8)) & 1) else 1

    def serre_w2(f_coeffs, ram_primes):
        d = len(f_coeffs) - 1
        e = [(-1) ** k * f_coeffs[k] for k in range(d + 1)]
        s = [Rational(d)]
        for k in range(1, 2 * d - 1):
            val = Rational(0)
            for j in range(1, min(k, d)):
                val += ((-1) ** (j - 1)) * e[j] * s[k - j]
            if k <= d:
                val += ((-1) ** (k - 1)) * k * e[k]
            else:
                val += ((-1) ** (d - 1)) * e[d] * s[k - d]
            s.append(val)
        G = Matrix(d, d, lambda i, j: s[i + j])
        assert int(G.det()) == int(Poly(f_coeffs, x, domain='ZZ').discriminant())
        M = G.copy()
        diag = []
        for k in range(d):
            diag.append(M[k, k])
            for i in range(k + 1, d):
                fac = M[i, k] / M[k, k]
                for j in range(k, d):
                    M[i, j] -= fac * M[k, j]
        res = {}
        for p in [0, 2] + list(ram_primes):
            w = 1
            for i in range(d):
                for j in range(i + 1, d):
                    w *= hilbert_rat(diag[i], diag[j], p)
            res[p] = w
        prod_v = 1
        for v in res.values():
            prod_v *= v
        assert prod_v == 1
        return res

    w_10931 = serre_w2([1, -2, -18, -15, 18, 17], [17, 643])
    w_11699 = serre_w2([1, -2, -13, 37, -21, -1], [11699])
    w_5567 = serre_w2([1, -1, -15, 36, -21, 1], [19, 293])
    assert w_10931 == {0: 1, 2: 1, 17: -1, 643: -1}
    assert w_11699 == {0: 1, 2: 1, 11699: 1}
    assert w_5567 == {0: 1, 2: 1, 19: 1, 293: 1}
    print(f"[PASS] 4C. Serre w_2(Tr(x^2)): A_5(10931^2)={w_10931} [obstructed]; A_5(11699^2)={w_11699} [embeds in 2.A_5!]; A_5(5567^2)={w_5567} [embeds!].")

    # 4D. Verify SL_2(F_5) = 2.A_5 element order distribution (V_4 -> Q_8 Regime B, cyclic -> abelian Regime A)
    sl2 = [(a, b, c, d) for a in range(5) for b in range(5) for c in range(5) for d in range(5) if (a * d - b * c) % 5 == 1]
    assert len(sl2) == 120

    def mm(X, Y):
        return (
            (X[0] * Y[0] + X[1] * Y[2]) % 5, (X[0] * Y[1] + X[1] * Y[3]) % 5,
            (X[2] * Y[0] + X[3] * Y[2]) % 5, (X[2] * Y[1] + X[3] * Y[3]) % 5,
        )

    ords = {}
    for X in sl2:
        cur, k = X, 1
        while cur != (1, 0, 0, 1):
            cur = mm(cur, X)
            k += 1
        ords[k] = ords.get(k, 0) + 1
    assert sorted(ords.items()) == [(1, 1), (2, 1), (3, 20), (4, 30), (5, 24), (6, 20), (10, 24)]
    print("[PASS] 4D. SL_2(F_5) has unique involution -I => preimage of V_4 is Q_8 (Regime B), preimages of C_2,C_3,C_5 are C_4,C_6,C_10 (Regime A).")


def main():
    t_start = time.time()
    run_suite_1()
    run_suite_2()
    run_suite_3()
    run_suite_4()
    print("\n" + "=" * 78)
    print(f"ALL 4 SUITES PASSED WITH ZERO ERRORS/WARNINGS in {time.time() - t_start:.2f}s!")
    print("=" * 78)


if __name__ == "__main__":
    main()
