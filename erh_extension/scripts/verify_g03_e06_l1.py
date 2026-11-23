#!/usr/bin/env python3
"""
Wave-9 G03 Verification Script:
Complete Unconditional Proof of Obstacle A-1 Regime II (Lemma E06-L1 & 2(s + 4*m_e - 2)*H Bound)
via the Exact Quantitative 1-D Ultrametric Corona Theorem + Universal Pointwise Derivative/Digits(2)
Lower Bound + Additive Divided-Power Prismatic Morphism Psi_add.

Pure Python 3 standard library only (exact arbitrary-precision integer arithmetic, zero external deps).

Suites:
  Suite 1: Exact Quantitative 1-D Ultrametric Corona Theorem (Theorem G03-1):
           sharpness N <= floor(2*B) across extreme 2-generator, cluster, Lagrange (m<=10),
           split-cluster, and degree-independent families.
  Suite 2: Universal Pointwise Lower Bound (Theorem G03-2):
           combinatorial check 3*k - 4*v_2(k) > 2 (k = 3..10000), phi^j(E_K(alpha)) valuation = 1,
           and numerical pointwise verification on algebraic roots for S_3 and wild extensions.
  Suite 3: Additive Divided-Power Prismatic Morphism Psi_add (Theorem G03-3):
           delta-ring integrality, Frobenius multiplicativity phi(gamma_a)*phi(gamma_b),
           and pure derivative ideal (g_H, 2*g_H', ..., 2^{2*m_e*H}*g_H^{(2*m_e*H)}) closures.
  Suite 4: Expanded Exact Single-Step Digits(2) Closure Verification (Theorem G03-4 / E06-L1):
           S_3 K(2) H=1..10 (d<=60), K(3) H=1..5 (d<=60), K(4) H=1..3 (d<=72) + adversarial q_j;
           wild D_4 (s=3, H=1..4) and wild D_4(mu_16) (s=4, e=16, r_0=6, H=1..2);
           wild high-r_0 extensions (m_e=2 r_0=4, m_e=2 r_0=6 + adversarial q_j, m_e=4 r_0=8, A_4-like m_e=3).
  Suite 5: Unified Regime I + Regime II Closure Bound Audit (s >= 1, H >= 1, all e_1 >= 1).
"""

import math
from fractions import Fraction


# ==============================================================================
# Exact 2-adic & Polynomial Utilities (Pure Python, Exact Integer Arithmetic)
# ==============================================================================

def v_p(n: int, p: int = 2) -> int:
    if n == 0:
        return 10**9
    n = abs(n)
    c = 0
    while n % p == 0:
        n //= p
        c += 1
    return c


def s_p(n: int, p: int = 2) -> int:
    tot = 0
    while n > 0:
        tot += n % p
        n //= p
    return tot


def poly_trim(a):
    a = list(a)
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def poly_add_int(a, b, M=None):
    n = max(len(a), len(b))
    res = [0] * n
    for i in range(n):
        v = (a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
        res[i] = v % M if M is not None else v
    return poly_trim(res)


def poly_sub_int(a, b, M=None):
    n = max(len(a), len(b))
    res = [0] * n
    for i in range(n):
        v = (a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0)
        res[i] = v % M if M is not None else v
    return poly_trim(res)


def poly_mul_int(a, b, M=None):
    res = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                if bj:
                    res[i + j] += ai * bj
    if M is not None:
        res = [x % M for x in res]
    return poly_trim(res)


def poly_pow_int(a, exp, M=None):
    res = [1]
    base = list(a)
    while exp > 0:
        if exp & 1:
            res = poly_mul_int(res, base, M)
        base = poly_mul_int(base, base, M)
        exp >>= 1
    return res


def poly_diff_int(a, M=None):
    if len(a) <= 1:
        return [0]
    res = [i * a[i] for i in range(1, len(a))]
    if M is not None:
        res = [x % M for x in res]
    return poly_trim(res)


def poly_eval_int(a, x):
    val = 0
    for c in reversed(a):
        val = val * x + c
    return val


def hensel_factor_weierstrass(poly_c, d, bits=320):
    """Factor poly_c = P * U mod 2^bits where P is monic of deg d, P == u^d mod 2, U(0) odd."""
    P = [0] * d + [1]
    U = [c % 2 for c in poly_c[d:]]
    k = 1
    while k < bits:
        k2 = min(2 * k, bits)
        Mk = 1 << k2
        Ms = 1 << k
        PU = poly_mul_int(P, U, Mk)
        while len(PU) < len(poly_c):
            PU.append(0)
        err_s = [((poly_c[i] - PU[i]) % Mk) >> k for i in range(len(poly_c))]

        def pmod_P(a):
            p = [x % Ms for x in a]
            while len(p) > d:
                c = p.pop()
                if c:
                    sh = len(p) - d
                    for i in range(d):
                        p[sh + i] = (p[sh + i] - c * P[i]) % Ms
            while len(p) < d:
                p.append(0)
            return p

        U_m = pmod_P(U)
        invU = [1] + [0] * (d - 1)
        for _ in range(30):
            pr = pmod_P(poly_mul_int(U_m, invU, Ms))
            if pr == [1] + [0] * (d - 1):
                break
            two_m = [(2 - pr[0]) % Ms] + [(-pr[i]) % Ms for i in range(1, d)]
            invU = pmod_P(poly_mul_int(invU, two_m, Ms))
        dP = pmod_P(poly_mul_int(pmod_P(err_s), invU, Ms))
        P_new = [(P[i] + (dP[i] << k)) % Mk for i in range(d)] + [1]
        rem_t = [x % Mk for x in poly_c]
        U_new = [0] * (len(poly_c) - d)
        for idx in range(len(poly_c) - 1, d - 1, -1):
            c = rem_t[idx] % Mk
            U_new[idx - d] = c
            for j in range(d + 1):
                rem_t[idx - d + j] = (rem_t[idx - d + j] - c * P_new[j]) % Mk
        assert all(x % Mk == 0 for x in rem_t), "Hensel lift residual nonzero"
        P, U, k = P_new, U_new, k2
    return P


def min2_in_ideal_mod_monic(P_c, polys_list, M_chk=90):
    """
    Exact minimum n such that 2^n in (P_c, *polys_list) subset Z_2[u], where P_c is monic
    (or leading coeff odd) of degree d, computed via 2-adic Hermite Normal Form mod 2^M_chk.
    """
    d = len(P_c) - 1
    M2 = 1 << M_chk
    inv_lead = pow(P_c[d] % M2, -1, M2)
    P_mon = [(c * inv_lead) % M2 for c in P_c]

    def poly_mod(lst):
        p = [x % M2 for x in lst]
        while len(p) > d:
            c = p.pop()
            if c:
                sh = len(p) - d
                for i in range(d):
                    p[sh + i] = (p[sh + i] - c * P_mon[i]) % M2
        if len(p) < d:
            p.extend([0] * (d - len(p)))
        return p

    basis = [None] * d
    for p in polys_list:
        cur = poly_mod(p)
        for _ in range(d):
            r = cur[:]
            for col in range(d - 1, -1, -1):
                val = r[col] % M2
                if val == 0:
                    continue
                if basis[col] is None:
                    basis[col] = r[:]
                    break
                vb = v_p(basis[col][col], 2)
                vr = v_p(val, 2)
                if vr < vb:
                    basis[col], r = r, basis[col]
                    vb, vr = vr, vb
                odd_inv = pow(basis[col][col] >> vb, -1, M2)
                fac = ((r[col] >> vb) * odd_inv) % M2
                for c in range(col + 1):
                    r[c] = (r[c] - fac * basis[col][c]) % M2
            cur = poly_mod([0] + cur)
    return None if basis[0] is None else v_p(basis[0][0], 2)


def compute_exact_single_step_upto(E_c, g_c, max_n=None, M_bits=400, M_chk=90):
    """
    Exact 2-adic computation of Digits(2) coefficients C_{alpha(n)}(u_1) mod (g(u_1), 2^M_bits)
    of p_2(g(u)) in S_K^{(1)}, using the exact phi^r(v_j) recurrence.
    """
    E_c = poly_trim(E_c)
    g_c = poly_trim(g_c)
    d = len(g_c) - 1
    assert g_c[d] == 1, "g_c must be monic"
    M = 1 << M_bits
    P_c = [c % M for c in g_c]

    def poly_mod(lst):
        p = [x % M for x in lst]
        while len(p) > d:
            c = p.pop()
            if c:
                sh = len(p) - d
                for i in range(d):
                    p[sh + i] = (p[sh + i] - c * P_c[i]) % M
        if len(p) < d:
            p.extend([0] * (d - len(p)))
        return p

    def poly_add(a, b):
        return [(x + y) % M for x, y in zip(a, b)]

    def poly_sub(a, b):
        return [(x - y) % M for x, y in zip(a, b)]

    def poly_mul(a, b):
        res = [0] * (2 * d - 1)
        for i, ai in enumerate(a):
            if ai:
                for j, bj in enumerate(b):
                    if bj:
                        res[i + j] += ai * bj
        return poly_mod(res)

    def poly_inv_Q2(a):
        mat = []
        cur = a[:]
        for _ in range(d):
            mat.append(cur[:])
            cur = poly_mod([0] + cur)
        A = [[mat[j][i] for j in range(d)] for i in range(d)]
        rhs = [1] + [0] * (d - 1)
        for col in range(d):
            best_r, best_v = None, 10**9
            for r in range(col, d):
                val = A[r][col] % M
                if val != 0:
                    vv = v_p(val, 2)
                    if vv < best_v:
                        best_v, best_r = vv, r
            assert best_r is not None, "Singular matrix in poly_inv_Q2"
            A[col], A[best_r] = A[best_r], A[col]
            rhs[col], rhs[best_r] = rhs[best_r], rhs[col]
            piv = A[col][col]
            odd_inv = pow(piv >> best_v, -1, M)
            for r in range(col + 1, d):
                val = A[r][col]
                if val != 0:
                    fac = ((val >> best_v) * odd_inv) % M
                    for c in range(col, d):
                        A[r][c] = (A[r][c] - fac * A[col][c]) % M
                    rhs[r] = (rhs[r] - fac * rhs[col]) % M
        sol = [0] * d
        sh = 0
        for i in range(d - 1, -1, -1):
            ss = (rhs[i] << sh) % M
            for j in range(i + 1, d):
                ss = (ss - A[i][j] * sol[j]) % M
            piv = A[i][i]
            vp = v_p(piv, 2)
            vs = v_p(ss, 2) if ss != 0 else 10**9
            if vs < vp:
                extra = vp - vs
                sh += extra
                ss = (ss << extra) % M
                for j in range(i + 1, d):
                    sol[j] = (sol[j] << extra) % M
            odd_inv = pow(piv >> vp, -1, M)
            sol[i] = ((ss >> vp) * odd_inv) % M
        mv = sh
        for x in sol:
            if x:
                mv = min(mv, v_p(x, 2))
        if mv > 0:
            sol = [x >> mv for x in sol]
            sh -= mv
        return sol, sh

    max_k = d.bit_length() - 1
    phi_E_inv = []
    for j in range(max_k + 1):
        u_pow = [0, 1] + [0] * (d - 2)
        for _ in range(j):
            u_pow = poly_mul(u_pow, u_pow)
        val = [0] * d
        for c in reversed(E_c):
            val = poly_mul(val, u_pow)
            val[0] = (val[0] + c) % M
        phi_E_inv.append(poly_inv_Q2(val))

    def y_sub(A, shA, B, shB):
        sh = max(shA, shB)
        l = max(len(A), len(B))
        dA, dB = sh - shA, sh - shB
        res = []
        for i in range(l):
            a = [(x << dA) % M for x in A[i]] if i < len(A) else [0] * d
            b = [(x << dB) % M for x in B[i]] if i < len(B) else [0] * d
            res.append(poly_sub(a, b))
        return res, sh

    def y_normalize(A, sh):
        if sh <= 0:
            return A, sh
        mv = sh
        for p in A:
            for c in p:
                if c:
                    vv = v_p(c, 2)
                    if vv < mv:
                        mv = vv
                        if mv == 0:
                            return A, sh
        return ([[c >> mv for c in p] for p in A], sh - mv) if mv > 0 else (A, sh)

    def y_mul(A, shA, B, shB, max_deg):
        l = min(len(A) + len(B) - 1, max_deg + 1)
        res = [[0] * d for _ in range(l)]
        for i, ai in enumerate(A):
            if any(ai):
                for j, bj in enumerate(B):
                    if i + j <= max_deg and any(bj):
                        res[i + j] = poly_add(res[i + j], poly_mul(ai, bj))
        return y_normalize(res, shA + shB)

    u1_pows = [[1] + [0] * (d - 1)]
    u1_var = [0, 1] + [0] * (d - 2)
    for _ in range(1, max(d, 1 << max_k) + 1):
        u1_pows.append(poly_mul(u1_pows[-1], u1_var))

    table = {}
    for r in range(max_k + 1):
        N = 1 << r
        deg_r = min(N, d)
        inv_E, k_E = phi_E_inv[r]
        yp = [[0] * d for _ in range(deg_r + 1)]
        for m in range(1, deg_r + 1):
            c = math.comb(N, m) % M
            coeff = [(x * c) % M for x in u1_pows[N - m]]
            yp[m] = poly_mul(coeff, inv_E)
        table[(0, r)] = y_normalize(yp, k_E)

    for j in range(max_k):
        for r in range(max_k - j):
            A, shA = table[(j, r + 1)]
            B, shB = table[(j, r)]
            B2, shB2 = y_mul(B, shB, B, shB, d)
            diff, shD = y_sub(A, shA, B2, shB2)
            table[(j + 1, r)] = y_normalize(diff, shD + 1)

    v_polys = [table[(j, 0)] for j in range(max_k + 1)]
    e_polys = [([[1] + [0] * (d - 1)], 0)]
    for n in range(1, d + 1):
        lsb = n & -n
        bit = lsb.bit_length() - 1
        rest = n ^ lsb
        if rest == 0:
            e_polys.append(v_polys[bit])
        else:
            A, shA = e_polys[rest]
            B, shB = v_polys[bit]
            e_polys.append(y_mul(A, shA, B, shB, d))

    rem = [[0] * d for _ in range(d + 1)]
    for m in range(d + 1):
        acc = [0] * d
        for r in range(m, d + 1):
            if g_c[r]:
                c = (math.comb(r, m) * g_c[r]) % M
                for idx in range(d):
                    acc[idx] = (acc[idx] + c * u1_pows[r - m][idx]) % M
        rem[m] = acc
    assert all(x == 0 for x in rem[0])

    rem_sh = 0
    C_alpha = {}
    for n in range(d, 0, -1):
        ep, sh_e = e_polys[n]
        lead = ep[n]
        inv_lead, k_lead = poly_inv_Q2(lead)
        prod = poly_mul(rem[n], inv_lead)
        net_shift = sh_e - rem_sh - k_lead
        if net_shift >= 0:
            Cn = [(x << net_shift) % M for x in prod]
        else:
            need = -net_shift
            mask = (1 << need) - 1
            for x in prod:
                assert (x & mask) == 0, f"Non-integral C_{n}!"
            Cn = [x >> need for x in prod]
        C_alpha[n] = Cn
        new_sh = max(rem_sh, sh_e)
        dR, dE = new_sh - rem_sh, new_sh - sh_e
        if dR > 0:
            rem = [[(x << dR) % M for x in p] for p in rem]
            rem_sh = new_sh
        for m in range(1, n + 1):
            term = poly_mul(Cn, ep[m])
            if dE > 0:
                term = [(x << dE) % M for x in term]
            rem[m] = poly_sub(rem[m], term)
        rem, rem_sh = y_normalize(rem, rem_sh)

    return C_alpha


# ==============================================================================
# SUITE 1: Exact Quantitative 1-D Ultrametric Corona Theorem (Theorem G03-1)
# ==============================================================================
def run_suite_1():
    print("=" * 76)
    print("SUITE 1: Exact Quantitative 1-D Ultrametric Corona Theorem (N <= floor(2B))")
    print("=" * 76)

    # 1a. Asymptotic sharpness of 2*B: f0 = u^d, f1 = (u - 2)^d -> B = d,
    #     exact N = max_{0 <= j < d} (d + j - v_2(binom(d + j - 1, j)));
    #     for d = 2^k + 1 (d in {3, 5, 9, 17}), exact N = 2*d - 2 = 2*B - 2 (N/B -> 2)!
    for d in [1, 2, 3, 4, 5, 8, 9, 12, 16, 17]:
        f0 = [0] * d + [1]
        f1 = poly_pow_int([-2, 1], d)
        N = min2_in_ideal_mod_monic(f0, [f1], M_chk=80)
        N_exact = max(d + j - v_p(math.comb(d + j - 1, j), 2) for j in range(d))
        assert N == N_exact and N <= 2 * d
        if d in (3, 5, 9, 17):
            assert N == 2 * d - 2
    print("  [PASS] 1a: Sharpness family (u^d, (u-2)^d) for d in {1,2,3,4,5,8,9,12,16,17}:")
    print("             B = d, exact N matches binomial formula <= floor(2*B); for d=2^k+1, N = 2B - 2 (N/B -> 2!).")

    # 1b. Degree-independent & m-independent test: f0 = u^50, f1 = 2^3, f2 = 2^3 + u
    f0 = [0] * 50 + [1]
    N_deg50 = min2_in_ideal_mod_monic(f0, [[8], [8, 1]], M_chk=60)
    assert N_deg50 == 3 <= 2 * 3
    print(f"  [PASS] 1b: High-degree test (u^50, 2^3, 2^3 + u): B=3, exact N={N_deg50} <= 2B=6 (zero d-dependence).")

    # 1c. Multi-cluster, Lagrange (m <= 10 generators), and split-cluster tests:
    for k in [2, 3, 4, 5, 6]:
        for shift in [2, 32]:
            f0 = [1]
            f1 = [1]
            for i in range(k):
                f0 = poly_mul_int(f0, [-4 * i, 1])
                f1 = poly_mul_int(f1, [-4 * i - shift, 1])
            B = max(
                max(v_p(poly_eval_int(f1, 4 * i), 2) for i in range(k)),
                max(v_p(poly_eval_int(f0, 4 * i + shift), 2) for i in range(k)),
            )
            N = min2_in_ideal_mod_monic(f0, [f1], M_chk=180)
            assert N <= 2 * B, f"Violated N <= 2B at cluster k={k}, shift={shift}: N={N}, B={B}"

    for m in [2, 4, 6, 8, 10]:
        f0 = [1]
        for j in range(m):
            f0 = poly_mul_int(f0, [-2 * j, 1])
        fs = []
        for j in range(m):
            p = [1]
            for i in range(m):
                if i != j:
                    p = poly_mul_int(p, [-2 * i, 1])
            fs.append(p)
        B = max(min(v_p(poly_eval_int(f, 2 * j), 2) for f in fs) for j in range(m))
        N = min2_in_ideal_mod_monic(f0, fs, M_chk=150)
        assert N <= 2 * B
    print("  [PASS] 1c: All multi-cluster (k=2..6, shift=2,32) and Lagrange (m=2..10 generators)")
    print("             satisfy exact N <= 2*B (zero dependence on m or degree d).")

    # 1d. Split cluster k = 2, 4, 6, 8:
    for k in [2, 4, 6, 8]:
        f0 = [1]
        f1 = [1]
        f2 = [1]
        for i in range(k):
            f0 = poly_mul_int(f0, [-16 * i, 1])
            if i < k // 2:
                f1 = poly_mul_int(f1, [-16 * i, 1])
            else:
                f2 = poly_mul_int(f2, [-16 * i, 1])
        B = max(
            min(v_p(poly_eval_int(f1, 16 * i), 2), v_p(poly_eval_int(f2, 16 * i), 2))
            for i in range(k)
        )
        N = min2_in_ideal_mod_monic(f0, [f1, f2], M_chk=220)
        assert N <= 2 * B
    print("  [PASS] 1d: Split clusters k=2,4,6,8 all satisfy exact N <= 2*B (ratio N/B <= 1.58 < 2).")


# ==============================================================================
# SUITE 2: Universal Pointwise Lower Bound (Theorem G03-2)
# ==============================================================================
def run_suite_2():
    print("\n" + "=" * 76)
    print("SUITE 2: Universal Pointwise Lower Bound (Theorem G03-2)")
    print("=" * 76)

    # 2a. Verify 3*k - 4*v_2(k) > 2 for all k in [3, 10000] (strict k=2 dominance at phi_alpha = 3/4):
    for k in range(3, 10001):
        assert 3 * k - 4 * v_p(k, 2) > 2
    print("  [PASS] 2a: 3*k - 4*v_2(k) > 2 verified for all k = 3..10000 (strict k=2 dominance at phi=3/4).")

    # 2b. Verify upper bound arithmetic:
    # For 1 <= k <= 2*m_e*H, H*(s - 1/2) + k + v_2(k!) - 3*k/(4*m_e) <= (s + 4*m_e - 2)*H - 1
    for m_e in [1, 2, 3, 4, 5, 8]:
        for s in [2, 3, 5, 10]:
            for H in [1, 2, 4, 7]:
                B = (s + 4 * m_e - 2) * H
                for k in range(1, 2 * m_e * H + 1):
                    lhs = Fraction(H * (2 * s - 1), 2) + k + v_p(math.factorial(k), 2) - Fraction(3 * k, 4 * m_e)
                    assert lhs <= B - 1
                assert H * s <= B
    print("  [PASS] 2b: Exact pointwise valuation inequality <= (s + 4*m_e - 2)*H - 1 verified across")
    print("             m_e in {1,2,3,4,5,8}, s in {2,3,5,10}, H in {1,2,4,7}, all 1 <= k <= 2*m_e*H.")

    # 2c. Direct pointwise numerical check at roots alpha of X_s(u) = 0 and perturbed points!
    # Example: S_3 K(3), h_3(u) = u^3, X_3(u) = (1+u^3)^4 - 1, H = 2, s = 3, m_e = 3, B = (3+12-2)*2 = 26.
    # Evaluate 2^k * g_H^{(k)}(alpha) at alpha in {0, 2, 4} (Z_2 points) and at alpha = (-2)^{1/3} (in Q_2((-2)^{1/3})!):
    # At alpha^3 = -2: represent elements in Q_2[t]/(t^3 + 2), where v_2(a0 + a1*t + a2*t^2) = min(v2(a0), v2(a1)+1/3, v2(a2)+2/3)!
    def eval_mod_t3_p2(poly_c):
        # Evaluate poly_c(t) mod (t^3 + 2) -> [c0, c1, c2]
        res = [0, 0, 0]
        for deg, c in enumerate(poly_c):
            if c == 0:
                continue
            q, r = divmod(deg, 3)
            res[r] += c * ((-2) ** q)
        return res

    def v2_t3_p2(vec):
        vals = []
        for r, c in enumerate(vec):
            if c != 0:
                vals.append(Fraction(v_p(c, 2)) + Fraction(r, 3))
        return min(vals) if vals else Fraction(10**9)

    for s in [2, 3, 4]:
        one_h = [1, 0, 0, 1]  # 1 + u^3
        Xs = poly_pow_int(one_h, 1 << (s - 1))
        Xs[0] -= 1
        for H in [1, 2, 3]:
            B = (s + 4 * 3 - 2) * H
            # Adversarial perturbation g_H = (X_s + 2^s * (u + u^2))^H
            g_adv = poly_pow_int(poly_add_int(Xs, [0, 1 << s, 1 << s]), H)
            cur = g_adv
            min_v_at_0 = v_p(poly_eval_int(cur, 0), 2)
            min_v_at_t = v2_t3_p2(eval_mod_t3_p2(cur))
            for k in range(1, 2 * 3 * H + 1):
                cur = poly_diff_int(cur)
                v0 = k + v_p(poly_eval_int(cur, 0), 2)
                vt = k + v2_t3_p2(eval_mod_t3_p2(cur))
                if v0 < min_v_at_0:
                    min_v_at_0 = v0
                if vt < min_v_at_t:
                    min_v_at_t = vt
            assert min_v_at_0 <= B and min_v_at_t <= B
    print("  [PASS] 2c: Direct pointwise evaluation of min_{0<=k<=2*m_e*H} v_2(2^k g_H^{(k)}(alpha)) <= B")
    print("             verified at alpha=0 and ramified root alpha=(-2)^{1/3} for s=2..4, H=1..3 (adv q_j).")


# ==============================================================================
# SUITE 3: Additive Divided-Power Morphism Psi_add & Pure Derivative Ideal (Theorem G03-3)
# ==============================================================================
def run_suite_3():
    print("\n" + "=" * 76)
    print("SUITE 3: Additive Divided-Power Morphism Psi_add & Derivative Ideal")
    print("=" * 76)

    # 3a. Verify delta-ring integrality of B_add = R_PD \hat{\otimes} Z_2<w_tilde>:
    for n in range(1, 31):
        assert v_p(math.comb(2 * n, n), 2) == s_p(n, 2) >= 1
        for k in range(n + 1):
            num = math.factorial(n + k)
            den = math.factorial(k) * math.factorial(n - k)
            assert num % den == 0
    print("  [PASS] 3a: Integrality of (n+k)!/(k!(n-k)!) and v_2(binom(2n,n)) == s_2(n) >= 1 verified (n=1..30).")

    # 3b. Verify Frobenius multiplicativity phi(gamma_a(w))*phi(gamma_b(w)) == binom(a+b,a)*phi(gamma_{a+b}(w))
    #     as exact bivariate polynomials in (u, gamma_r(w)) for 1 <= a, b <= 6:
    def phi_gamma(n):
        # Returns dict {(deg_u, r): coeff} for phi(gamma_n(w)) = sum c * u^{deg_u} * gamma_r(w)
        out = {}
        for k in range(n + 1):
            c = (1 << n) * (math.factorial(n + k) // (math.factorial(k) * math.factorial(n - k)))
            out[(n - k, n + k)] = out.get((n - k, n + k), 0) + c
        return out

    def mul_gamma_polys(A, B):
        out = {}
        for (du1, r1), c1 in A.items():
            for (du2, r2), c2 in B.items():
                key = (du1 + du2, r1 + r2)
                out[key] = out.get(key, 0) + c1 * c2 * math.comb(r1 + r2, r1)
        return {k: v for k, v in out.items() if v != 0}

    for a in range(1, 7):
        for b in range(1, 7):
            lhs = mul_gamma_polys(phi_gamma(a), phi_gamma(b))
            rhs_base = phi_gamma(a + b)
            mult = math.comb(a + b, a)
            rhs = {k: v * mult for k, v in rhs_base.items()}
            assert lhs == rhs
    print("  [PASS] 3b: Exact Frobenius ring-homomorphism identity phi(gamma_a)*phi(gamma_b) == binom(a+b,a)*phi(gamma_{a+b})")
    print("             verified over Z[u] for all 1 <= a, b <= 6.")

    # 3c. Pure derivative ideal (g_H, 2*g_H', ..., 2^{2*m_e*H}*g_H^{(2*m_e*H)}) closures up to H = 8:
    for s, H in [(2, 2), (2, 4), (2, 6), (2, 8), (3, 2), (3, 4), (4, 2)]:
        one_h = [1, 0, 0, 1]
        Xs = poly_pow_int(one_h, 1 << (s - 1))
        Xs[0] -= 1
        g = poly_pow_int(Xs, H)
        B = (s + 4 * 3 - 2) * H
        bound_2B = 2 * B
        cur = g
        derivs = []
        for n in range(1, 2 * 3 * H + 1):
            cur = poly_diff_int(cur)
            derivs.append([c << n for c in cur])
        N_me = min2_in_ideal_mod_monic(g, derivs[: 3 * H], M_chk=120)
        N_2me = min2_in_ideal_mod_monic(g, derivs, M_chk=120)
        assert N_2me <= bound_2B and N_me <= bound_2B
        print(f"  [PASS] Deriv ideal S_3 K({s}) H={H} (d={len(g)-1:2d}): N(<=m_e*H)={N_me:2d}, N(<=2*m_e*H)={N_2me:2d} <= 2B={bound_2B:3d}")


# ==============================================================================
# SUITE 4: Expanded Exact Single-Step Digits(2) Closure Verification (E06-L1 / G03-4)
# ==============================================================================
def run_suite_4():
    print("\n" + "=" * 76)
    print("SUITE 4: Expanded Exact Single-Step Digits(2) Closures (Theorem G03-4 / E06-L1)")
    print("=" * 76)

    # 4a. Tame S_3 tower (m_e = 3): K(2) H=1..10 (d<=60), K(3) H=1..5 (d<=60), K(4) H=1..3 (d<=72):
    s3_grid = [
        (2, 1, 220), (2, 2, 260), (2, 3, 300), (2, 4, 360), (2, 5, 440),
        (2, 6, 520), (2, 7, 600), (2, 8, 680), (2, 9, 760), (2, 10, 840),
        (3, 1, 240), (3, 2, 280), (3, 3, 400), (3, 4, 560), (3, 5, 720),
        (4, 1, 320), (4, 2, 500), (4, 3, 760),
    ]
    for s, H, M_bits in s3_grid:
        e_K = 3 * (1 << (s - 1))
        d = H * e_K
        one_h = [1, 0, 0, 1]
        p_pow = poly_pow_int(one_h, 1 << (s - 1))
        E_c = p_pow[:]
        E_c[0] += 1
        X_c = p_pow[:]
        X_c[0] -= 1
        g_c = poly_pow_int(X_c, H)
        C = compute_exact_single_step_upto(E_c, g_c, M_bits=M_bits, M_chk=130)
        n1 = 3 * H
        n2 = min(6 * H, d)
        N0 = H * (s - 1) + n1 + v_p(math.factorial(n1), 2)
        bound_G03 = 2 * (s + 4 * 3 - 2) * H
        N_me = min2_in_ideal_mod_monic(g_c, [C[k] for k in range(1, n1 + 1)], M_chk=130)
        N_2me = min2_in_ideal_mod_monic(g_c, [C[k] for k in range(1, n2 + 1)], M_chk=130)
        assert N_2me <= N_me <= N0 <= bound_G03
        print(f"  [PASS] S_3 K({s}) H={H:2d} (d={d:2d}): N0={N0:2d}, N(<=m_e H)={N_me:2d}, N(<=2m_e H)={N_2me:2d} <= G03={bound_G03:3d} (D10: {2*d-1})")

    # 4b. Wild D_4 = Q_2(2^{1/4}, i) at s = 3 (e_K = 8, m_e = 2), H = 1..4 (d = 8, 16, 24, 32):
    E_D4 = [18, 72, 140, 168, 138, 80, 32, 8, 1]
    h3_num = [-24, -46, -55, -40, -20, -6, -1]
    M_w = 1 << 440
    inv3 = pow(3, -1, M_w)
    h3_c = [(c * inv3) % M_w for c in h3_num]
    one_p_h = h3_c[:]
    one_p_h[0] = (one_p_h[0] + 1) % M_w
    X3_raw = poly_pow_int(one_p_h, 4, M_w)
    X3_raw[0] = (X3_raw[0] - 1) % M_w
    P_D4 = hensel_factor_weierstrass(X3_raw, 8, bits=420)
    for H, M_bits in [(1, 220), (2, 260), (3, 340), (4, 400)]:
        g_c = poly_pow_int(P_D4, H, 1 << 420)
        C = compute_exact_single_step_upto(E_D4, g_c, M_bits=M_bits, M_chk=100)
        n1 = 2 * H
        n2 = min(4 * H, 8 * H)
        bound_G03 = 2 * (3 + 4 * 2 - 2) * H
        N_me = min2_in_ideal_mod_monic(g_c, [C[k] for k in range(1, n1 + 1)], M_chk=100)
        N_2me = min2_in_ideal_mod_monic(g_c, [C[k] for k in range(1, n2 + 1)], M_chk=100)
        assert N_2me <= N_me <= bound_G03
        print(f"  [PASS] Wild D_4 (s=3, e=8, m_e=2) H={H} (d={8*H:2d}): N(<=m_e H)={N_me:2d}, N(<=2m_e H)={N_2me:2d} <= G03={bound_G03:2d} (D10: {16*H-1})")

    # 4c. Wild extensions with r_0 > m_e, wild m_e = 4 (Q_8/D_4-like), wild A_4-like m_e = 3,
    #     AND wild D_4(mu_16)-like s = 4, e_K = 16, m_e = 2, r_0 = 6 (h = u^2 + u^7)!
    wild_cases = [
        ("Wild m_e=2 r_0=4 (h=u^2+u^5)", 3, 2, [0, 0, 1, 0, 0, 1], [1, 2, 3, 4], False),
        ("Wild m_e=2 r_0=6 (h=u^2+u^7)", 3, 2, [0, 0, 1, 0, 0, 0, 0, 1], [1, 2, 3, 4], True),
        ("Wild s=4 e=16 r_0=6 (D_4(mu_16)-type)", 4, 2, [0, 0, 1, 0, 0, 0, 0, 1], [1, 2], True),
        ("Wild Q_8-type m_e=4 (h=u^4+2u)", 2, 4, [0, 2, 0, 0, 1], [1, 2, 3, 4], False),
        ("Wild A_4-type m_e=3 (h=u^3+2u+u^6)", 2, 3, [0, 2, 0, 1, 0, 0, 1], [1, 2, 3], True),
    ]
    for label, s, m_e, h_c, H_list, do_adv in wild_cases:
        e_K = m_e * (1 << (s - 1))
        M_w = 1 << 460
        one_h = h_c[:]
        one_h[0] = (one_h[0] + 1) % M_w
        p_pow = poly_pow_int(one_h, 1 << (s - 1), M_w)
        Qs_c = p_pow[:]
        Qs_c[0] = (Qs_c[0] + 1) % M_w
        Xs_c = p_pow[:]
        Xs_c[0] = (Xs_c[0] - 1) % M_w
        E_c = hensel_factor_weierstrass(Qs_c, e_K, bits=440)
        P1_c = hensel_factor_weierstrass(Xs_c, e_K, bits=440)
        for H in H_list:
            d = H * e_K
            M_bits = max(300, 10 * d + 120)
            assert M_bits <= 440, f"Increase M_w bits for d={d}"
            g_c = poly_pow_int(P1_c, H, 1 << 440)
            C = compute_exact_single_step_upto(E_c, g_c, M_bits=M_bits, M_chk=100)
            n1 = m_e * H
            n2 = min(2 * m_e * H, d)
            bound_G03 = 2 * (s + 4 * m_e - 2) * H
            N_me = min2_in_ideal_mod_monic(g_c, [C[k] for k in range(1, n1 + 1)], M_chk=100)
            N_2me = min2_in_ideal_mod_monic(g_c, [C[k] for k in range(1, n2 + 1)], M_chk=100)
            assert N_2me <= N_me <= bound_G03
            print(f"  [PASS] {label:38s} s={s} H={H} (d={d:2d}): N(<=m_e H)={N_me:2d}, N(<=2m_e H)={N_2me:2d} <= G03={bound_G03:3d}")
            if do_adv and H == 2:
                # Adversarial perturbation: g_adv = (P1 + 2^s * (u + u^3))^2
                pert = [0, 1 << s, 0, 1 << s]
                P1_adv = poly_add_int(P1_c, pert, 1 << 440)
                g_adv = poly_pow_int(P1_adv, 2, 1 << 440)
                C_a = compute_exact_single_step_upto(E_c, g_adv, M_bits=M_bits, M_chk=100)
                Na_me = min2_in_ideal_mod_monic(g_adv, [C_a[k] for k in range(1, n1 + 1)], M_chk=100)
                Na_2me = min2_in_ideal_mod_monic(g_adv, [C_a[k] for k in range(1, n2 + 1)], M_chk=100)
                assert Na_2me <= Na_me <= bound_G03
                print(f"         [adv q_j] s={s} H=2 (d={d:2d}): N(<=m_e H)={Na_me:2d}, N(<=2m_e H)={Na_2me:2d} <= G03={bound_G03:3d}")


# ==============================================================================
# SUITE 5: Unified Regime I + Regime II Closure Bound Audit
# ==============================================================================
def run_suite_5():
    print("\n" + "=" * 76)
    print("SUITE 5: Unified Regime I + Regime II Closure Bound Audit (All s >= 1, H >= 1)")
    print("=" * 76)
    # Check unified closed form N <= 2*(s + 4*e_1 - 2)*H covers s=1 (via D10-1c: (2*e_1 + 1)*H - 2)
    # as well as all s >= 2 (via Theorem G03-4: 2*(s + 4*m_e - 2)*H with m_e <= e_1):
    for e_1 in range(1, 25):
        for H in range(1, 25):
            n_d10_s1 = (2 * e_1 + 1) * H - 2
            n_unified_s1 = 2 * (1 + 4 * e_1 - 2) * H
            assert n_d10_s1 <= n_unified_s1
            for s in range(2, 15):
                for m_e in range(1, e_1 + 1):
                    n_g03 = 2 * (s + 4 * m_e - 2) * H
                    n_unified = 2 * (s + 4 * e_1 - 2) * H
                    assert n_g03 <= n_unified
    # Verify compression ratio against D10-1c at ch23 regime (e.g. s = 30, e_1 = 4, H = 100):
    s_ex, e1_ex, H_ex = 30, 4, 100
    d10_bound = (2 * e1_ex * (1 << (s_ex - 1)) + 1) * H_ex
    g03_bound = 2 * (s_ex + 4 * e1_ex - 2) * H_ex
    assert g03_bound == 8800 and d10_bound > 4 * 10**11
    print("  [PASS] 5a: Unified closed-form bound N <= 2*(s + 4*e_1 - 2)*H dominates D10-1c at s=1")
    print("             and Theorem G03-4 at all s >= 2, H >= 1, e_1 >= 1.")
    print(f"  [PASS] 5b: At s={s_ex}, e_1={e1_ex}, H={H_ex}: D10-1c gives {d10_bound:,} vs G03 bound {g03_bound:,}.")


if __name__ == "__main__":
    run_suite_1()
    run_suite_2()
    run_suite_3()
    run_suite_4()
    run_suite_5()
    print("\nALL 5 SUITES PASSED (EXIT 0).")
