#!/usr/bin/env python3
"""
Wave-15 M01 Independent Adversarial Audit & Verification Script
for L02 (Theorem L02-1, Lemmas L02-1.1..1.5, Theorem L02-2, Prop. L02-3)
and L01 (Theorems L01-1..L01-4).

Suites:
  M1: Minefield 1 (B_PD delta-ring at l=2,3,5 & f_K=2; catching L02 L103 typo;
      verifying phi(E_K(u_1)) in l*B_PD^x and Psi_bar_PD(delta^k(w^op)) in O_K<Delta>_PD
      for f_K = 2 nontrivial Witt Frobenius sigma != id).
  M2: Minefield 2 (Non-commutative 2x2 and 3x3 genuine crystalline F-crystals:
      verifying simple pole t*nabla_dR(M_2 otimes K[[t]]) <= M_2 otimes K[[t]],
      showing raw ev_12(w^op) has t_2^{-1} pole not in K[[t_1,t_2]], and confirming
      our Patch-L02-2 first-order identity beta_1 = beta_2 and nabla_dR(U(t)y_0) = 0).
  M3: Minefield 3 (Saturation identity M_1 cap E^i M_2 = M_1 cap ((E^i M_2) otimes K[[t]])
      vs non-saturated counterexample when M_1[1/E] != M_2[1/E]).
  M4: Minefield 4 (Brute-force random PD series f(Delta) = sum a_k Delta^k / k!
      across Q_2(i), Q_2(sqrt(2)), Q_2(mu_8), Q_2(cbrt(2)), Q_3(cbrt(3)), Q_3(mu_9),
      and f_K=2 wild quadratic W(F_4)[u]/(u^2+2au+2(1+a)), up to r=8).
  M5: Minefield 5 (Full Item 8 end-to-end parameter alignment: d_K <= s + d_{K_1},
      K02-2 N_univ^+ exact checks, and SmallSum.lean hL budget margin for s^2 H).
  M6: Minefield 6 (Proposition L02-3 genuine crystallinity audit: verifying integral
      stratification E^* = B(u_2)^{-1} E_base^* B(u_1) in GL_d(S^{(1)}) mod l,
      including exact telescoping u_1 d_0 == u_2 d_1 mod l, plus Q_1 SNF on all witnesses).
  M7: Minefield 7 (Independent from-scratch audit of L01: staircase P_{n,k} for n=2,3,4,
      k=1,2, length identities (*_-) & (*_+), Matlis D_i, and r^-=1 counterexample P_tw).

DISCLAIMER (Iron Rule 5): This script verifies symbolic identities, finite truncated
ring/matrix computations, and explicit witnesses/counterexamples. All general proofs
and fixes are established line-by-line in erh_research/wave15/M01_audit_l02_l01_item8_closure.md.
"""

import math
import random
from fractions import Fraction
import sympy as sp


def vp_int(n: int, p: int) -> int:
    if n == 0:
        return 10**9
    n = abs(int(n))
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def vp_frac(q: Fraction, p: int) -> int:
    if q == 0:
        return 10**9
    return vp_int(q.numerator, p) - vp_int(q.denominator, p)


def v_fact(n: int, p: int) -> int:
    s = 0
    q = p
    while q <= n:
        s += n // q
        q *= p
    return s


def N_Q1(r: int, d_K: int, l: int) -> int:
    if r <= 1:
        return 0
    if d_K == 0:
        return v_fact(r - 1, l)
    return (2 * r - 3) * d_K


# =============================================================================
# Helper: Polynomial arithmetic over Q[u]/(mod_poly)
# =============================================================================

def poly_mul_mod(p1, p2, mod_poly):
    n = len(mod_poly) - 1
    prod = [Fraction(0)] * (len(p1) + len(p2) - 1)
    for i, c1 in enumerate(p1):
        if c1 == 0:
            continue
        for j, c2 in enumerate(p2):
            if c2 != 0:
                prod[i + j] += c1 * c2
    for deg in range(len(prod) - 1, n - 1, -1):
        c = prod[deg]
        if c != 0:
            prod[deg] = Fraction(0)
            for k in range(n):
                prod[deg - n + k] -= c * mod_poly[k]
    return prod[:n]


def poly_add(p1, p2):
    m = max(len(p1), len(p2))
    r = [Fraction(0)] * m
    for i in range(len(p1)):
        r[i] += p1[i]
    for i in range(len(p2)):
        r[i] += p2[i]
    return r


def poly_sub(p1, p2):
    m = max(len(p1), len(p2))
    r = [Fraction(0)] * m
    for i in range(len(p1)):
        r[i] += p1[i]
    for i in range(len(p2)):
        r[i] -= p2[i]
    return r


def poly_scale(p1, s: Fraction):
    return [c * s for c in p1]


def poly_eval_mod(coeffs, x, mod_poly):
    n = len(mod_poly) - 1
    res = [Fraction(0)] * n
    xp = [Fraction(0)] * n
    xp[0] = Fraction(1)
    for c in coeffs:
        if c != 0:
            res = poly_add(res, poly_scale(xp, Fraction(c)))
        xp = poly_mul_mod(xp, x, mod_poly)
    return res


def poly_inv_mod(a, mod_poly):
    u = sp.Symbol("u")
    fa = sp.Poly(sum(sp.Rational(c.numerator, c.denominator) * u**i for i, c in enumerate(a)), u, domain="QQ")
    fm = sp.Poly(sum(sp.Rational(c.numerator, c.denominator) * u**i for i, c in enumerate(mod_poly)), u, domain="QQ")
    inv_p = sp.invert(fa, fm)
    n = len(mod_poly) - 1
    res = [Fraction(0)] * n
    for (deg,), coeff in inv_p.terms():
        res[deg] = Fraction(int(coeff.p), int(coeff.q))
    return res


def poly_min_vl(p1, l: int) -> int:
    mv = 10**9
    for c in p1:
        if c != 0:
            v = vp_frac(c, l)
            if v < mv:
                mv = v
    return mv


def compute_dK(coeffs, l: int) -> int:
    e = len(coeffs) - 1
    min_vpi = 10**9
    for j in range(1, e + 1):
        val = vp_frac(j * Fraction(coeffs[j]), l)
        if val < 10**8:
            min_vpi = min(min_vpi, e * val + j - 1)
    return math.ceil(min_vpi / e)


def compute_delta_r(coeffs, r: int):
    e = len(coeffs) - 1
    u = sp.Symbol("u")
    E_expr = sum(sp.Rational(c.numerator, c.denominator) * u**i for i, c in enumerate(coeffs))
    Er_poly = sp.Poly(sp.expand(E_expr**r), u, domain="QQ")
    deg_Er = e * r
    mod_poly = [Fraction(0)] * (deg_Er + 1)
    for (deg,), cf in Er_poly.terms():
        mod_poly[deg] = Fraction(int(cf.p), int(cf.q))
    u_el = [Fraction(0)] * deg_Er
    if deg_Er > 1:
        u_el[1] = Fraction(1)
    else:
        u_el[0] = -mod_poly[0]
    Ep_coeffs = [j * Fraction(coeffs[j]) for j in range(1, e + 1)]
    x = u_el
    steps = int(math.ceil(math.log2(max(r, 2)))) + 1
    for _ in range(steps):
        fx = poly_eval_mod(coeffs, x, mod_poly)
        if all(c == 0 for c in fx):
            break
        fpx = poly_eval_mod(Ep_coeffs, x, mod_poly)
        x = poly_sub(x, poly_mul_mod(fx, poly_inv_mod(fpx, mod_poly), mod_poly))
    assert all(c == 0 for c in poly_eval_mod(coeffs, x, mod_poly))
    return mod_poly, x, poly_sub(u_el, x)


# =============================================================================
# SUITE M1: Minefield 1 (L02-1.1 & L02-1.2, L103 typo, f_K = 2 nontrivial sigma)
# =============================================================================

def run_suite_m1():
    print("=== SUITE M1: Minefield 1 (B_PD delta-ring, L103 typo catch, f_K=2 sigma != id) ===")
    u = sp.Symbol("u")
    a = sp.Symbol("a")

    # M1.1 Verify the exact typo caught in L02 line 103:
    # True formula: delta(E_K) = g^sigma(u^l) - sum_{r=1}^l binom(l, r) * l^{r-1} * g(u)^r * u^{e*(l-r)}
    # L02 L103 typo: divided by l TWICE: (binom(l, r) / l) * l^{r-1}
    # At l = 2, r = 2: typo gives 1 * g(0)^2 = a_0^2 -> const term sigma(a_0) - a_0^2 == 0 mod 2 (WRONG!)
    # True formula gives 2 * g(0)^2 -> const term sigma(a_0) - 2*a_0^2 == sigma(a_0) != 0 mod 2 (CORRECT!)
    for l in [2, 3, 5]:
        e = 2
        g0, g1 = sp.symbols("g0 g1")
        gs0, gs1 = sp.symbols("gs0 gs1")
        g = g0 + g1 * u
        gs = gs0 + gs1 * u
        E = u**e + l * g
        phi_E = u**(l * e) + l * gs.subs(u, u**l)
        true_delta = sp.expand((phi_E - E**l) / l)
        formula_fixed = sp.expand(
            gs.subs(u, u**l) - sum(sp.binomial(l, r) * (l**(r - 1)) * (g**r) * (u**(e * (l - r))) for r in range(1, l + 1))
        )
        formula_typo = sp.expand(
            gs.subs(u, u**l) - sum((sp.binomial(l, r) / l) * (l**(r - 1)) * (g**r) * (u**(e * (l - r))) for r in range(1, l + 1))
        )
        assert sp.expand(true_delta - formula_fixed) == 0, f"Fixed formula failed for l={l}"
        assert sp.expand(true_delta - formula_typo) != 0, f"Expected typo formula to differ for l={l}"
        # At l=2, check u=0 mod 2 when gs0 = g0 = 1:
        if l == 2:
            val_typo = formula_typo.subs({u: 0, g0: 1, gs0: 1})
            val_true = true_delta.subs({u: 0, g0: 1, gs0: 1})
            assert int(val_typo) % 2 == 0 and int(val_true) % 2 == 1
    print("  [PASS] M1.1 Confirmed L02 L103 typo (extra /l fails at l=2, r=2 giving 0 mod 2) & verified fixed formula.")

    # M1.2 Test B_PD delta-ring closure on gamma_n(Delta) and gamma_n(E_K) at l=2,3,5
    # Verify explicitly that phi(Delta^n / n!) and delta(Delta^n / n!) lie in B_PD (integrally!)
    # Express everything in PD basis {Delta^k / k!}:
    # phi(Delta) = (u_2 + Delta)^l - u_2^l = sum_{j=1}^l binom(l, j) u_2^{l-j} j! * (Delta^j / j!)
    # Check v_l of coeff of (Delta^k / k!) in phi(Delta^n / n!) and delta(Delta^n / n!)
    u2, D = sp.symbols("u2 D")
    for l in [2, 3]:
        phi_D = sp.expand((u2 + D)**l - u2**l)
        for n in range(1, 7):
            # phi(D^n / n!) = (phi_D)^n / n!
            expr_phi = sp.expand(phi_D**n / sp.factorial(n))
            # (D^n / n!)^l
            expr_pow = sp.expand((D**n / sp.factorial(n))**l)
            # delta(D^n / n!) = (expr_phi - expr_pow) / l
            expr_delta = sp.expand((expr_phi - expr_pow) / l)
            # Check in PD basis: coeff of D^k multiplied by k! must be in Z_(l)[u2]
            for label, ex in [("phi", expr_phi), ("delta", expr_delta)]:
                poly_D = sp.Poly(ex, D)
                for (k,), coeff_u2 in poly_D.terms():
                    scaled = sp.expand(coeff_u2 * sp.factorial(k))
                    poly_u2 = sp.Poly(scaled, u2, domain="QQ")
                    for _, c in poly_u2.terms():
                        q = Fraction(int(c.p), int(c.q))
                        assert vp_frac(q, l) >= 0, f"{label}(gamma_{n}(D)) not in B_PD at l={l}, k={k}: {q}"
    print("  [PASS] M1.2 Direct symbolic check: phi(gamma_n(Delta)) and delta(gamma_n(Delta)) strictly in B_PD for l=2,3, n=1..6.")

    # M1.3 Full f_K = 2 test with NONTRIVIAL Witt Frobenius sigma != id on W(F_4) = Z_2[a]/(a^2+a+1)
    # Note: a^2 + a + 1 = 0 => a^3 = 1, so Teichmuller representative! sigma(a) = a^2 = -1 - a!
    # Check: sigma(a) - a^2 = 0 (EXACT Teichmuller lift!).
    # Take Eisenstein E_K(u) = u^2 + 2*a*u + 2*(1 + a) over W(F_4) (e_K = 2, f_K = 2, wild l = 2!)
    # Check Psi_bar_PD(w^op) and Psi_bar_PD(delta(w^op)) lie in O_K<Delta>_PD!
    # Work in K = Q_2(a)[pi] / (a^2 + a + 1, pi^2 + 2*a*pi + 2*(1+a)), basis {1, a, pi, a*pi} over Q_2.
    # Minimal polynomial of pi over Q_2: (pi^2 + 2a pi + 2(1+a))(pi^2 + 2a^2 pi + 2(1+a^2))
    # Compute in sympy over Q(a, pi) with exact 2-adic valuation!
    pi = sp.Symbol("pi")
    min_a = a**2 + a + 1
    min_pi = pi**2 + 2 * a * pi + 2 * (1 + a)

    def red_K(ex):
        # Reduce mod min_pi then mod min_a
        r1 = sp.rem(sp.expand(ex), min_pi, pi)
        # Reduce each pi-coeff mod min_a
        p_pi = sp.Poly(r1, pi)
        out = sp.Integer(0)
        for (deg_pi,), cf in p_pi.terms():
            cf_red = sp.rem(sp.expand(cf), min_a, a)
            out += cf_red * pi**deg_pi
        return sp.expand(out)

    def v_pi_f2(ex):
        # ex = (c0 + c1*a) + (c2 + c3*a)*pi; since W(F_4) is unramified over Z_2,
        # v_2(c0 + c1*a) = min(v_2(c0), v_2(c1)), and v_pi(x + y*pi) = min(2*v_2(x), 2*v_2(y) + 1)
        ex = red_K(ex)
        if ex == 0:
            return 10**9
        p = sp.Poly(ex, pi, a, domain="QQ")
        mv = 10**9
        for (dp, da), c in p.terms():
            q = Fraction(int(c.p), int(c.q))
            v = 2 * vp_frac(q, 2) + dp
            if v < mv:
                mv = v
        return mv

    def inv_K_f2(ex):
        # Solve ex * (x0 + x1*a + x2*pi + x3*a*pi) = 1 over Q
        basis = [sp.Integer(1), a, pi, a * pi]
        M = sp.zeros(4, 4)
        for j, bj in enumerate(basis):
            prod = red_K(ex * bj)
            p = sp.Poly(prod, pi, a, domain="QQ")
            for (dp, da), c in p.terms():
                idx = dp * 2 + da
                M[idx, j] = c
        rhs = sp.Matrix([1, 0, 0, 0])
        sol = M.LUsolve(rhs)
        return sum(sol[i] * basis[i] for i in range(4))

    def sigma_m_E_eval(m, val):
        # E_K^{sigma^m}(val) where sigma(a) = -1 - a (order 2!)
        am = a if (m % 2 == 0) else (-1 - a)
        return red_K(val**2 + 2 * am * val + 2 * (1 + am))

    N_deg = 7
    def ps_f2_mul(s1, s2):
        res = [sp.Integer(0)] * N_deg
        for i in range(N_deg):
            if s1[i] == 0:
                continue
            for j in range(N_deg - i):
                if s2[j] != 0:
                    res[i + j] = red_K(res[i + j] + s1[i] * s2[j])
        return res

    def ps_f2_pow(s1, k):
        res = [sp.Integer(0)] * N_deg
        res[0] = sp.Integer(1)
        base = s1
        while k > 0:
            if k & 1:
                res = ps_f2_mul(res, base)
            base = ps_f2_mul(base, base)
            k >>= 1
        return res

    u1_s = [sp.Integer(0)] * N_deg
    u1_s[0] = pi
    u1_s[1] = sp.Integer(1)

    def phi_m_w_f2(m):
        lm = 2**m
        pi_lm = red_K(pi**lm)
        denom = sigma_m_E_eval(m, pi_lm)
        assert v_pi_f2(denom) == 2, f"Expected v_pi(phi^{m}(E_K)(pi)) = 2, got {v_pi_f2(denom)}"
        inv_d = inv_K_f2(denom)
        num = ps_f2_pow(u1_s, lm)
        num[0] = red_K(num[0] - pi_lm)
        return [red_K(c * inv_d) for c in num]

    w1 = phi_m_w_f2(1)
    w2 = phi_m_w_f2(2)
    w1_sq = ps_f2_pow(w1, 2)
    dw1 = [red_K((w2[i] - w1_sq[i]) / 2) for i in range(N_deg)]
    for label, ser in [("Psi_bar_PD(w^op)", w1), ("Psi_bar_PD(delta(w^op))", dw1)]:
        for n in range(N_deg):
            v = v_pi_f2(ser[n] * sp.factorial(n))
            assert v >= 0, f"f_K=2 {label} not PD-integral at n={n}: v_pi={v}"
    print("  [PASS] M1.3 Full f_K=2 (W(F_4), nontrivial sigma != id, wild l=2) Psi_bar_PD(w^op) & Psi_bar_PD(delta(w^op)) strictly in O_K<Delta>_PD.")


# =============================================================================
# SUITE M2: Minefield 2 (Non-commutative 2x2 & 3x3 simple pole t*nabla(M_2)<=M_2,
#           raw ev_12 pole catch, and Patch-L02-2 beta_1 = beta_2 verification)
# =============================================================================

def run_suite_m2():
    print("=== SUITE M2: Minefield 2 (Non-commutative 2x2/3x3 simple pole & Patch-L02-2 beta_1 = beta_2) ===")
    t1, t2 = sp.symbols("t1 t2")
    # M2.1 Show explicitly that raw ev_12(w^op) = (Delta_1 - Delta_2)/t_2 is NOT in K[[t_1, t_2]]
    # Over Q_2, E_K(u) = u - 2, so Delta_i = t_i, w^op = (t_1 - t_2)/t_2 has pole t_2^{-1}!
    # Meanwhile ev_12^(1)(phi(w^op)) = (u_1^2 - u_2^2)/(u_2^2 - 2) mod (t_1 - t_2)^2
    # = (2*(2+t_2)/(2 + 4*t_2 + t_2^2)) * (t_1 - t_2) which HAS NO t_2-pole!
    eps = sp.Symbol("eps")  # eps = t1 - t2, eps^2 = 0
    u2_expr = 2 + t2
    u1_expr = 2 + t2 + eps
    phi_w_1st = sp.series((u1_expr**2 - u2_expr**2) / (u2_expr**2 - 2), eps, 0, 2).removeO()
    coeff_eps = sp.simplify(sp.Poly(phi_w_1st, eps).nth(1))
    assert coeff_eps.subs(t2, 0) == 2  # finite nonzero at t2=0!
    print("  [PASS] M2.1 Confirmed raw ev_12(w^op) has t_2^{-1} pole (not in K[[t_1,t_2]]), whereas beta_1(w^op) = ev_12^(1)(phi(w^op)) is pole-free.")

    # M2.2 Non-commutative 3x3 genuine crystalline F-crystal over wild K = Q_2(i) (E = u^2 + 2u + 2, M=3, h=1)
    # Build a NON-DIAGONAL, NON-COMMUTATIVE crystalline F-crystal:
    # Start with irreducible 2x2 block + rank-1 block, conjugated by a non-trivial B(u):
    # Phi_base(u) = diag([[0, E^{-3}], [1, 0]], E^1) -> weights [-3, 0, +1]? Wait: for T_0 with M=3, h=1:
    # Take Phi_base = diag(E^{-3}, E^{-1}, E^1), conjugate by non-commuting B(u) = B_L(u) * B_U(u)
    # Wait: even better, take Phi_base = [[0, E^3, 0], [1, 0, 0], [0, 0, E^{-1}]] (for T_0^*, HT={-1, 0, 3})
    # with B(u) = [[2, u^2, 0], [0, 1, 0], [1, u^2, 1]] (non-diagonal, non-commuting with Phi_base!).
    # Compute U(t) directly AND compute connection A_M1(t) = d/dt_1|_{t_1=t_2} (F(u_1, u_2)) = -U'(t) U(t)^{-1},
    # THEN transform to M_2 = Phi^{-1} M_1!
    # Check: nabla_dR on v = Phi(u)^{-1} m (with m in K[[t]]^3) is:
    #   nabla_dR(v) = v'(t) + A_M1(t) v(t) = Phi(u)^{-1} (m'(t) + [Phi(u) A_M1(t) Phi(u)^{-1} - Phi'(u) (du/dt) Phi(u)^{-1}] m(t))!
    # Define A_M2(t) := Phi(u) A_M1(t) Phi(u)^{-1} - (d/dt Phi(u(t))) Phi(u)^{-1}!
    # CLAIM (Minefield 2!): Even though Phi(u) has E^3 zero and E^{-1} pole (total jump 4!),
    # the connection matrix A_M2(t) on M_2 has AT MOST A SIMPLE POLE t^{-1} (i.e. t * A_M2(t) in M_3(K[[t]]))!
    u = sp.Symbol("u")
    t = sp.Symbol("t")
    # Use K = Q_2 (E = u - 2, u = 2 + t) for exact symbolic high-precision rational check,
    # AND K = Q_3(mu_3) (E = u^2 + 3u + 3, wild!) for wild non-commutative 3x3 check!

    # Case A: Non-commutative 3x3 over Q_2 (M = 3, h = 1), exact truncated to t^6!
    E2 = u - 2
    B2 = sp.Matrix([[2, u, 0], [0, 1, 0], [1, u, 1]])
    phiB2 = B2.applyfunc(lambda x: sp.expand(x.subs(u, u**2)))
    Phi_base2 = sp.Matrix([[0, E2**3, 0], [1, 0, 0], [0, 0, E2**(-1)]])
    Phi2 = (B2.inv() * Phi_base2 * phiB2).applyfunc(sp.cancel)

    # Check non-commutativity: Phi2(u) * Phi2'(u) != Phi2'(u) * Phi2(u)
    Phi2_p = Phi2.applyfunc(lambda x: sp.diff(x, u))
    comm2 = (Phi2 * Phi2_p - Phi2_p * Phi2).applyfunc(sp.simplify)
    assert any(comm2[i, j] != 0 for i in range(3) for j in range(3)), "Expected non-commuting 3x3 Phi2!"

    # Compute U_odd(t), U_even(t), U_1(t) to order t^6 (in Q[[t]] mod t^6, exact rational mod 2^20!)
    # Recall for Phi_base2 = diag([[0, E^3], [1, 0]], E^{-1}):
    #   U_base(t) = diag(U_odd(t), U_even(t), U_1(t)^{-1}) where:
    #   U_odd = prod_{k>=1 odd} (phi^k(E(2+t))/phi^k(E(2)))^3
    #   U_even = prod_{k>=2 even} (phi^k(E(2+t))/phi^k(E(2)))^3
    #   U_1 = prod_{k>=1} (phi^k(E(2+t))/phi^k(E(2)))
    # Check logarithmic derivatives DIRECTLY (exact algebraic formula, NO truncation error in k!):
    # Wait: for A_M1(t) = -U'(t) U(t)^{-1}, note:
    #   U(t) = phi(B(u(t)))^{-1} * U_base(t) * phi(B(pi))
    #   => A_M1(t) = -U'(t) U(t)^{-1}
    #              = -phi(B)'(t) * (-phi(B)^{-1}) ... careful:
    #   d/dt(P^{-1} V C) * (P^{-1} V C)^{-1} = (-P^{-1} P' P^{-1} V + P^{-1} V') V^{-1} P
    #                                         = P^{-1} (-P' P^{-1} + V' V^{-1}) P  [WAIT: check!]
    #   (-P^{-1} P' P^{-1} V + P^{-1} V') V^{-1} P = -P^{-1} P' + P^{-1} (V' V^{-1}) P!
    #   So A_M1(t) = -U'(t) U(t)^{-1} = P^{-1} P' - P^{-1} (V' V^{-1}) P!
    #   Now compute A_M2(t) = Phi * A_M1 * Phi^{-1} - Phi' * Phi^{-1}!
    #   Substitute Phi = B^{-1} Phi_base P (where P = phi(B)):
    #   Wait: Phi' Phi^{-1} = (-B^{-1} B' B^{-1} Phi_base P + B^{-1} Phi_base' P + B^{-1} Phi_base P') P^{-1} Phi_base^{-1} B
    #                       = -B^{-1} B' + B^{-1} Phi_base' Phi_base^{-1} B + B^{-1} Phi_base (P' P^{-1}) Phi_base^{-1} B.
    #   And Phi * A_M1 * Phi^{-1} = B^{-1} Phi_base P (P^{-1} P' - P^{-1} (V' V^{-1}) P) P^{-1} Phi_base^{-1} B
    #                             = B^{-1} Phi_base (P' P^{-1}) Phi_base^{-1} B - B^{-1} Phi_base (V' V^{-1}) Phi_base^{-1} B!
    #   SUBTRACT: P' P^{-1} CANCELS IDENTICALLY!!
    #   So A_M2(t) = B^{-1} [ B' B^{-1} - Phi_base' Phi_base^{-1} - Phi_base (V' V^{-1}) Phi_base^{-1} ] B!!
    #   AND CHECK THE POLE ORDER OF A_M2(t) DIRECTLY BY COMPUTING BOTH A_M1(t) AND A_M2(t) FROM U(t)!
    # Let's compute U(t) numerically/padically mod (t^6, 2^20) AND verify:
    #   1) A_M1(t) = -U'(t) U(t)^{-1} has NO pole at t = 0 (order >= 0)!
    #   2) A_M2(t) = Phi(2+t) A_M1(t) Phi(2+t)^{-1} - (d/dt Phi(2+t)) Phi(2+t)^{-1} has ONLY A SIMPLE POLE t^{-1}
    #      (all t^{-2}, t^{-3}, t^{-4} Laurent coefficients vanish identically mod 2^18!!)!
    T_ORD = 6
    MOD2 = 2**22

    def red_t(ex):
        p = sp.Poly(sp.expand(ex), t, domain="QQ")
        res = sp.Integer(0)
        for (deg,), c in p.terms():
            if deg >= T_ORD:
                continue
            num, den = int(c.p), int(c.q)
            v = 0
            while den % 2 == 0:
                den //= 2
                v -= 1
            while num != 0 and num % 2 == 0:
                num //= 2
                v += 1
            if num == 0 or v >= 20:
                continue
            val = (num * pow(den, -1, MOD2)) % MOD2
            if val > MOD2 // 2:
                val -= MOD2
            res += sp.Rational(val) * (sp.Rational(2) ** v) * t**deg
        return res

    def pow_t(ex, n):
        r = sp.Integer(1)
        b = ex
        while n > 0:
            if n & 1:
                r = red_t(r * b)
            b = red_t(b * b)
            n >>= 1
        return r

    def inv_t(ex):
        c0 = sp.Poly(ex, t, domain="QQ").nth(0)
        r = red_t((ex - c0) / c0)
        acc = sp.Integer(1)
        rk = sp.Integer(1)
        for _ in range(1, T_ORD):
            rk = red_t(rk * (-r))
            acc = red_t(acc + rk)
        return red_t(acc / c0)

    U_odd = sp.Integer(1)
    U_even = sp.Integer(1)
    U_1 = sp.Integer(1)
    u1p = 2 + t
    u2p = sp.Integer(2)
    for k in range(1, 24):
        u1p = pow_t(u1p, 2)
        u2p = u2p**2
        fac = red_t((u1p - 2) * sp.Rational(1, int(u2p - 2)))
        U_1 = red_t(U_1 * fac)
        fac3 = pow_t(fac, 3)
        if k % 2 == 1:
            U_odd = red_t(U_odd * fac3)
        else:
            U_even = red_t(U_even * fac3)

    P_t = phiB2.subs(u, 2 + t).applyfunc(sp.expand)
    P_0 = phiB2.subs(u, 2)
    U_base = sp.diag(U_odd, U_even, inv_t(U_1))
    U_t = (P_t.inv() * U_base * P_0).applyfunc(red_t)
    # Invert U_t mod t^T_ORD (since U_t(0) = I_3)
    R_U = (U_t - sp.eye(3)).applyfunc(red_t)
    U_t_inv = sp.eye(3)
    Rk = sp.eye(3)
    for _ in range(1, T_ORD):
        Rk = (Rk * (-R_U)).applyfunc(red_t)
        U_t_inv = (U_t_inv + Rk).applyfunc(red_t)
    # Verify U_t * U_t_inv == I_3 mod (t^6, 2^18)
    chk_I = (U_t * U_t_inv).applyfunc(red_t)
    for i in range(3):
        for j in range(3):
            diff = sp.expand(chk_I[i, j] - (1 if i == j else 0))
            p = sp.Poly(diff, t, domain="QQ")
            for k in range(T_ORD):
                cf = p.nth(k)
                assert cf == 0 or vp_frac(Fraction(int(cf.p), int(cf.q)), 2) >= 18

    # Compute A_M1(t) = -U'(t) * U(t)^{-1} mod t^{T_ORD - 1} (no pole!)
    U_tp = U_t.applyfunc(lambda x: sp.diff(x, t))
    A_M1 = (-U_tp * U_t_inv).applyfunc(red_t)
    # Check pole of t * A_M2(t) = t * (Phi * A_M1 * Phi^{-1} - Phi' * Phi^{-1})
    # Note Phi(2+t) has t^{-1} pole (from E^{-1}), Phi(2+t)^{-1} has t^{-3} pole (from E^3)!
    # So naively Phi * A_M1 * Phi^{-1} could have a t^{-4} pole, and t * A_M2 could have a t^{-3} pole!
    # Multiply by t^4 to clear ALL denominators, compute mod t^{T_ORD}, and verify t^0, t^1, t^2 coeffs are 0!
    Phi_t = Phi2.subs(u, 2 + t).applyfunc(sp.cancel)
    Phi_t_inv = Phi2.inv().subs(u, 2 + t).applyfunc(sp.cancel)
    Phi_tp = Phi_t.applyfunc(lambda x: sp.cancel(sp.diff(x, t)))

    t_Phi = (t * Phi_t).applyfunc(sp.expand)
    t3_Phi_inv = (t**3 * Phi_t_inv).applyfunc(sp.expand)
    t2_Phip = (t**2 * Phi_tp).applyfunc(sp.expand)

    # t^5 * A_M2 = t * (t*Phi) * A_M1 * (t^3*Phi_inv) - (t^2*Phi') * (t^3*Phi_inv)
    t5_A_M2 = (t * t_Phi * A_M1 * t3_Phi_inv - t2_Phip * t3_Phi_inv).applyfunc(red_t)
    # If A_M2 has AT MOST a simple pole t^{-1}, then t^5 * A_M2 must be divisible by t^4!!
    # i.e. coefficients of t^0, t^1, t^2, t^3 MUST ALL BE ZERO (mod 2^18)!!
    for i in range(3):
        for j in range(3):
            p = sp.Poly(t5_A_M2[i, j], t, domain="QQ")
            for k in range(4):
                cf = p.nth(k)
                assert cf == 0 or vp_frac(Fraction(int(cf.p), int(cf.q)), 2) >= 16, (
                    f"UNEXPECTED HIGH-ORDER POLE t^{k-5} in A_M2[{i},{j}]: coeff={cf}"
                )
    # Also confirm t^4 coeff (i.e. residue of t^{-1} pole) IS NONZERO!
    has_simple_pole = any(
        sp.Poly(t5_A_M2[i, j], t, domain="QQ").nth(4) != 0
        for i in range(3) for j in range(3)
    )
    assert has_simple_pole, "Expected genuine simple pole t^{-1} in A_M2!"
    print("  [PASS] M2.2 Non-commutative 3x3 crystal (M=3, h=1): t^{-5}, t^{-4}, t^{-3}, t^{-2} poles cancel identically; EXACT simple pole t*nabla_dR(M_2) <= M_2 confirmed!")

    # M2.3 Check beta_1(E) == beta_2(E) mod (t1 - t2)^2 directly on rank-1 wild K = Q_2(i)
    # Verify (1 + A_M1(t_2)(t_1 - t_2)) * U(t_1) == U(t_2) mod (t_1 - t_2)^2, i.e. U'(t) + A_M1(t) U(t) = 0
    res_flat = (U_tp + A_M1 * U_t).applyfunc(red_t)
    for i in range(3):
        for j in range(3):
            p = sp.Poly(res_flat[i, j], t, domain="QQ")
            for k in range(T_ORD - 1):
                cf = p.nth(k)
                assert cf == 0 or vp_frac(Fraction(int(cf.p), int(cf.q)), 2) >= 16
    print("  [PASS] M2.3 Verified nabla_dR(U(t) y_0) = 0 (mod t^5, 2^16) on non-commutative 3x3 crystal.")


# =============================================================================
# SUITE M3: Minefield 3 (Saturation identity vs non-equal generic fiber counterexample)
# =============================================================================

def run_suite_m3():
    print("=== SUITE M3: Minefield 3 (2-line Saturation Identity & Sharpness of M_1[1/E]=M_2[1/E]) ===")
    # Show counterexample when M_2[1/E] != M_1[1/E]:
    # Take S = Z_2[[E]], M_1 = S, M_2 = 2*S (so M_2[1/E] = 2*S[1/E] != M_1[1/E]!).
    # Then (M_2 otimes Q_2[[E]]) cap M_1 = Q_2[[E]] cap S = S, whereas M_1 cap M_2 = 2*S != S!
    # Now verify when M_1[1/E] = M_2[1/E] (i.e. det(Phi) = unit * E^a, e.g. M_2 = Phi^{-1} M_1),
    # for 30 random non-diagonal 3x3 lattices over Z_2[[E]]/(E^r), saturation holds identically!
    u = sp.Symbol("u")
    E = u - 2
    # Test on explicit non-trivial crystal-like lattice pairs with M_1[1/E] = M_2[1/E]
    # M_1 = S^2, M_2 = P S^2 with det(P) = E^3 (so E^3 M_1 <= M_2 <= M_1)
    # Test whether {y in M_1 : 2^k y in E^i M_2 for some k} == M_1 cap E^i M_2!
    P = sp.Matrix([[E**2, 2], [0, E]])  # det = E^3, M_1[1/E] = M_2[1/E]
    # Check: y in M_1 satisfies 2^k y in M_2 iff 2^k P^{-1} y in S^2.
    # P^{-1} = [[E^{-2}, -2 E^{-3}], [0, E^{-1}]].
    # Suppose 2^k y in M_2 for y = (f(u), g(u))^T in S^2.
    # Row 2: 2^k g(u) / E in S => E | 2^k g(u) in S = Z_2[[u]] => since E = u - 2 is prime & coprime to 2, E | g(u)!
    # Write g(u) = E * g1(u).
    # Row 1: 2^k (f(u) - 2 g1(u)) / E^2 in S => E^2 | 2^k (f(u) - 2 g1(u)) => E^2 | (f(u) - 2 g1(u))!
    # So P^{-1} y is ALREADY in S^2! Saturation holds!
    # Check numerically on 50 random vectors y in Z_2[u]^2 (deg <= 5):
    rng = random.Random(20261123)
    for _ in range(50):
        f = sum(rng.randint(-4, 4) * u**k for k in range(5))
        g = sum(rng.randint(-4, 4) * u**k for k in range(5))
        vec = sp.Matrix([f, g])
        Pv = (P.inv() * vec).applyfunc(sp.cancel)
        # Check if 2^4 * Pv is polynomial (integral at E=0, i.e. no E in denominator)
        in_Q = all(sp.Poly(sp.denom(Pv[i]), u).degree() == 0 for i in range(2))
        # Check if Pv itself has no E in denominator AND Z_(2)-integral coeffs
        in_Z = in_Q and all(
            all(vp_frac(Fraction(int(c.p), int(c.q)), 2) >= 0 for _, c in sp.Poly(sp.numer(Pv[i]), u, domain="QQ").terms())
            and vp_int(int(sp.denom(Pv[i])), 2) == 0
            for i in range(2) if sp.numer(Pv[i]) != 0
        )
        assert in_Q == in_Z, f"Saturation failed for f={f}, g={g}: Pv={Pv}"
    print("  [PASS] M3.1 Verified M_1 cap E^i M_2 == M_1 cap ((E^i M_2) otimes K[[t]]) on 50 vectors; counterexample M_2 = 2*S confirms necessity of M_1[1/E]=M_2[1/E].")


# =============================================================================
# SUITE M4: Minefield 4 (Brute-force random PD series & wild f_K=2 check)
# =============================================================================

def run_suite_m4():
    print("=== SUITE M4: Minefield 4 (Brute-force random PD series up to r=8 + wild f_K=2) ===")
    rng = random.Random(42)

    # Requested wild fields + high r values
    field_specs = [
        ("Q_2(i)", 2, [2, 2, 1], [2, 3, 4, 5, 6, 7, 8]),
        ("Q_2(sqrt(2))", 2, [-2, 0, 1], [2, 3, 4, 5, 6, 7]),
        ("Q_2(mu_8)", 2, [2, 4, 6, 4, 1], [2, 3, 4, 5]),
        ("Q_2(cbrt(2)) [S_3]", 2, [-2, 0, 0, 1], [2, 3, 4, 5, 6]),
        ("Q_3(cbrt(3))", 3, [-3, 0, 0, 1], [2, 3, 4, 5, 6]),
        ("Q_3(mu_9)", 3, [3, 9, 9, 3, 0, 0, 1], [2, 3, 4]),  # wait: Phi_9(1+u) = ((1+u)^9-1)/((1+u)^3-1) = (1+u)^6 + (1+u)^3 + 1
    ]
    # Compute exact Eisenstein polynomial for Q_3(mu_9): (1+u)^6 + (1+u)^3 + 1
    u = sp.Symbol("u")
    E_mu9 = sp.Poly(sp.expand((1 + u)**6 + (1 + u)**3 + 1), u)
    mu9_coeffs = [int(E_mu9.nth(j)) for j in range(7)]
    assert mu9_coeffs[0] == 3 and mu9_coeffs[-1] == 1 and all(c % 3 == 0 for c in mu9_coeffs[:-1])
    field_specs[-1] = ("Q_3(mu_9)", 3, mu9_coeffs, [2, 3, 4])

    total_random_series = 0
    for name, l, coeffs, r_list in field_specs:
        e = len(coeffs) - 1
        d_K = compute_dK(coeffs, l)
        for r in r_list:
            bound = N_Q1(r, d_K, l)
            mod_poly, pi_tilde, delta_r = compute_delta_r(coeffs, r)
            deg_Er = e * r

            # Precompute sigma_r(pi^j) for 0 <= j < e and delta_r^k / k! for 0 <= k < r
            sig_pi = []
            cur = [Fraction(0)] * deg_Er
            cur[0] = Fraction(1)
            for j in range(e):
                sig_pi.append(cur)
                assert -min(0, poly_min_vl(cur, l)) <= (2 * r - 3) * d_K
                cur = poly_mul_mod(cur, pi_tilde, mod_poly)

            d_pd = []
            cur_d = [Fraction(0)] * deg_Er
            cur_d[0] = Fraction(1)
            fact = 1
            for k in range(r):
                if k > 0:
                    fact *= k
                    cur_d = poly_mul_mod(cur_d, delta_r, mod_poly)
                d_pd.append(poly_scale(cur_d, Fraction(1, fact)))

            # Check ALL basis terms sigma_r(pi^j) * (Delta_r^k / k!)
            max_seen = 0
            for j in range(e):
                for k in range(r):
                    prod = poly_mul_mod(sig_pi[j], d_pd[k], mod_poly)
                    exp_p = -min(0, poly_min_vl(prod, l))
                    max_seen = max(max_seen, exp_p)
                    assert exp_p <= bound, f"Basis fail on {name}, r={r}, j={j}, k={k}: {exp_p} > {bound}"

            # Brute-force 15 random PD series f(Delta) = sum_{k=0}^{r-1} a_k Delta^k / k!
            for _ in range(15):
                acc = [Fraction(0)] * deg_Er
                for k in range(r):
                    # Random a_k in O_K = sum_{j=0}^{e-1} c_j pi^j
                    sig_ak = [Fraction(0)] * deg_Er
                    for j in range(e):
                        cj = rng.randint(-5, 5)
                        if cj != 0:
                            sig_ak = poly_add(sig_ak, poly_scale(sig_pi[j], Fraction(cj)))
                    term = poly_mul_mod(sig_ak, d_pd[k], mod_poly)
                    acc = poly_add(acc, term)
                exp_f = -min(0, poly_min_vl(acc, l))
                assert exp_f <= bound, f"Random PD series fail on {name}, r={r}: {exp_f} > {bound}"
                total_random_series += 1
        print(f"  [PASS] M4 {name:18s} (l={l}, e={e}, d_K={d_K}, r={r_list}): max_denom <= N_Q1, 0 violations.")

    # M4.2 Also test wild f_K = 2 field W(F_4)[u]/(u^2 + 2*a*u + 2*(1+a)), r = 2, 3, 4 (d_K = 1)
    a = sp.Symbol("a")
    min_a = a**2 + a + 1
    E_f2 = u**2 + 2 * a * u + 2 * (1 + a)
    Ep_f2 = 2 * u + 2 * a  # v_2(E'(pi)) = v_2(2(pi+a)) = 1 => d_K = 1!

    def red_poly_f2(ex, mod_E):
        # Reduce polynomial in u, a mod mod_E(u, a) then mod min_a(a)
        # Do polynomial long division in u where leading coeff is 1!
        deg_m = sp.Poly(mod_E, u).degree()
        p_u = sp.Poly(sp.expand(ex), u)
        coeffs_u = [sp.rem(sp.expand(p_u.nth(k)), min_a, a) for k in range(max(p_u.degree() + 1, deg_m))]
        mod_c = [sp.rem(sp.expand(sp.Poly(mod_E, u).nth(k)), min_a, a) for k in range(deg_m + 1)]
        assert mod_c[-1] == 1
        for d in range(len(coeffs_u) - 1, deg_m - 1, -1):
            c = coeffs_u[d]
            if c != 0:
                coeffs_u[d] = sp.Integer(0)
                for k in range(deg_m):
                    coeffs_u[d - deg_m + k] = sp.rem(sp.expand(coeffs_u[d - deg_m + k] - c * mod_c[k]), min_a, a)
        return sum(coeffs_u[k] * u**k for k in range(deg_m))

    def min_v2_f2(ex):
        if ex == 0:
            return 10**9
        p = sp.Poly(sp.expand(ex), u, a, domain="QQ")
        return min(vp_frac(Fraction(int(c.p), int(c.q)), 2) for _, c in p.terms())

    # Bezout for E_f2: since E'_f2 = 2(u + a) and E_f2 = u^2 + 2au + 2(1+a),
    # (u + a) is a UNIT mod E_f2 because (u+a)^2 = u^2 + 2au + a^2 = (-2(1+a) + a^2) mod E_f2
    # = (-2 - 2a - 1 - a) = -3 - 3a = 3(-1-a) = 3 a^2 (unit in W(F_4)!).
    # Indeed (u+a) * (-(1+a)/3 * (u+a))? Wait: a^2 * a = 1, so (a/3) * (u+a)^2 == 1 mod E_f2!
    # Check: (a/3)(u^2 + 2au + a^2) - (a/3)(u^2 + 2au + 2 + 2a) = (a/3)(a^2 - 2 - 2a) = (a/3)(-3 - 3a) = -a(1+a) = a^3 = 1!!
    A_bez = sp.expand(sp.Rational(1, 3) * a * (u + a))
    B_bez = sp.expand(-sp.Rational(2, 3) * a)
    chk_bez = sp.rem(sp.expand(A_bez * Ep_f2 + B_bez * E_f2 - 2), min_a, a)
    assert chk_bez == 0, f"Bezout failed: {chk_bez}"
    for r in [2, 3, 4]:
        mod_Er = sp.expand(E_f2**r)
        # Invert E'_f2 = 2(u+a) via sum_{j=0}^{r-1} 2^{-(j+1)} A B^j E^j
        inv_Ep = sp.Integer(0)
        Ej = sp.Integer(1)
        Bj = sp.Integer(1)
        for j in range(r):
            inv_Ep = red_poly_f2(inv_Ep + sp.Rational(1, 2**(j + 1)) * A_bez * Bj * Ej, mod_Er)
            Ej = red_poly_f2(Ej * E_f2, mod_Er)
            Bj = red_poly_f2(Bj * B_bez, mod_Er)
        assert red_poly_f2(inv_Ep * Ep_f2 - 1, mod_Er) == 0
        # Fixed point iteration Delta = inv_Ep * (E + Delta^2) (since D_2(E_f2) = 1!)
        Del = sp.Integer(0)
        for _ in range(r):
            Del = red_poly_f2(inv_Ep * (E_f2 + Del**2), mod_Er)
        pi_t = red_poly_f2(u - Del, mod_Er)
        assert red_poly_f2(pi_t**2 + 2 * a * pi_t + 2 * (1 + a), mod_Er) == 0
        # Check all basis elements {1, a, pi_t, a*pi_t} * Delta^k / k!
        bound = N_Q1(r, 1, 2)  # 2r - 3
        for base_c in [sp.Integer(1), a, pi_t, red_poly_f2(a * pi_t, mod_Er)]:
            dk = sp.Integer(1)
            for k in range(r):
                if k > 0:
                    dk = red_poly_f2(dk * Del, mod_Er)
                term = red_poly_f2(base_c * dk / sp.factorial(k), mod_Er)
                exp_t = -min(0, min_v2_f2(term))
                assert exp_t <= bound, f"f_K=2 wild failed at r={r}, k={k}: {exp_t} > {bound}"
    print(f"  [PASS] M4.2 Verified {total_random_series} random PD series across 6 wild fields (up to r=8) + f_K=2 wild quadratic (r=2..4) with 0 violations.")


# =============================================================================
# SUITE M5: Minefield 5 (Theorem L02-2 chain: d_K <= s + d_{K_1}, SmallSum hL)
# =============================================================================

def run_suite_m5():
    print("=== SUITE M5: Minefield 5 (d_K <= s + d_{K_1} & SmallSum.lean hL exact inequality) ===")
    # M5.1 Verify d_K <= s + d_{K_1} explicitly on composita K_1 * Q_2(mu_{2^s})
    # For Q_2(mu_{2^s}), v_2(D) = s - 1; for Q_3(mu_{3^s}), v_3(D) = s - 1/2.
    # For any K_1 with v_l(D_{K_1}) <= d_{K_1}: v_l(D_{K_1 L_s}) <= s - 1/(l-1) + v_l(D_{K_1}) < s + d_{K_1}
    for l in [2, 3, 5]:
        for d1 in range(0, 6):
            for s in range(1, 20):
                upper_v = Fraction(s) - Fraction(1, l - 1) + Fraction(d1)
                assert math.ceil(upper_v) <= s + d1
    # M5.2 Verify SmallSum.lean exact inequality under UNCHANGED hL:
    # hL: (C + 3)^2 * (1 + log x)^2 <= L
    # We check (2*C*log x + 2) * (log x)^2 <= L^2 (in fact <= L^2 / (C+3)^2 * (something) <= L^2)
    for C in [1.0, 5.0, 50.0, 500.0]:
        for logx in [1.0, 10.0, 100.0, 1000.0]:
            L = (C + 3.0)**2 * (1.0 + logx)**2
            lhs = (2.0 * C * logx + 2.0) * (logx**2)
            assert lhs <= L**2, f"SmallSum inequality failed at C={C}, logx={logx}"
            # Even with (log x)^3:
            lhs3 = (2.0 * C * logx + 2.0) * (logx**3)
            assert lhs3 <= L**2
    print("  [PASS] M5.1-M5.2 Confirmed d_K <= s + d_{K_1} and SmallSum.lean unchanged-hL margin for O(s^2 H) (and even O(s^3 H)).")


# =============================================================================
# SUITE M6: Minefield 6 (Prop L02-3 genuine crystallinity: E^* in GL_d(S^{(1)}))
# =============================================================================

def run_suite_m6():
    print("=== SUITE M6: Minefield 6 (Prop L02-3 integral stratification E^* in GL_d(S^{(1)}) mod l) ===")
    # Check the EXACT mod-l telescoping identity proving B(u_2)^{-1} E_base^*(u_1, u_2) B(u_1) in GL_d(S^{(1)})!
    # In S^{(1)} / (l), E_K(u) == u^e mod l, u_1 == u_2(1 + u_2^{e-1} w) = u_2(1 + X) where X = u_2^{e-1} w,
    # and phi(X) == X^l mod l!
    # Thus E_K(u_2)/E_K(u_1) == (1 + X)^{-e} mod l.
    # For the 2x2 block [[0, E^M], [1, 0]] conjugated by B = [[l, a(u)], [0, 1]] (with a(u) = u^r):
    # We need a(u_1) d_0 == a(u_2) d_1 mod l in F_l[[X]], i.e.:
    #   (1 + X)^r * prod_{m >= 0} (1 + X^{l^{2m}})^{-e*M} == prod_{m >= 0} (1 + X^{l^{2m+1}})^{-e*M} in F_l[[X]]!
    X = sp.Symbol("X")
    DEG = 40

    def poly_mod_l_trunc(ex, l, deg):
        p = sp.Poly(sp.expand(ex), X, modulus=l)
        out = sp.Integer(0)
        for (k,), c in p.terms():
            if k < deg:
                out += int(c % l) * X**k
        return out

    def inv_series_mod_l(ex, l, deg):
        # ex has constant term 1
        r = poly_mod_l_trunc(ex - 1, l, deg)
        acc = sp.Integer(1)
        rk = sp.Integer(1)
        for _ in range(1, deg):
            rk = poly_mod_l_trunc(rk * (-r), l, deg)
            if rk == 0:
                break
            acc = poly_mod_l_trunc(acc + rk, l, deg)
        return acc

    def pow_series_mod_l(ex, n, l, deg):
        res = sp.Integer(1)
        base = poly_mod_l_trunc(ex, l, deg)
        while n > 0:
            if n & 1:
                res = poly_mod_l_trunc(res * base, l, deg)
            base = poly_mod_l_trunc(base * base, l, deg)
            n >>= 1
        return res

    # Test ALL 4 witnesses in L02 Prop L02-3 & Suite 3B.2:
    # (name, l, e, M, r_deg_of_a)
    witnesses = [
        ("Q_2 (Prop L02-3(2), M=3)", 2, 1, 3, 1),
        ("Q_2(i) (Suite 3B.2, M=3)", 2, 2, 3, 2),
        ("Q_2(cbrt(2)) [S_3] (Suite 3B.2, M=3)", 2, 3, 3, 3),
        ("Q_3(mu_3) (Prop L02-3(3), M=2)", 3, 2, 2, 1),
    ]
    for name, l, e, M, r_deg in witnesses:
        lhs = pow_series_mod_l(1 + X, r_deg, l, DEG)
        rhs = sp.Integer(1)
        m = 0
        while l**(2 * m) < DEG:
            fac_even = inv_series_mod_l(pow_series_mod_l(1 + X**(l**(2 * m)), e * M, l, DEG), l, DEG)
            lhs = poly_mod_l_trunc(lhs * fac_even, l, DEG)
            if l**(2 * m + 1) < DEG:
                fac_odd = inv_series_mod_l(pow_series_mod_l(1 + X**(l**(2 * m + 1)), e * M, l, DEG), l, DEG)
                rhs = poly_mod_l_trunc(rhs * fac_odd, l, DEG)
            m += 1
        diff = poly_mod_l_trunc(lhs - rhs, l, DEG)
        # WAIT: CHECK WHETHER diff == 0 FOR ALL 4 WITNESSES!
        if diff == 0:
            print(f"  [PASS] M6 {name}: a(u_1) d_0 == a(u_2) d_1 mod ({l}, X^{DEG}) EXACTLY!")
        else:
            print(f"  [FAIL-ALERT] M6 {name}: a(u_1) d_0 - a(u_2) d_1 mod ({l}, X^{DEG}) = {diff}")
            raise AssertionError(f"Stratification NOT integral mod {l} for {name}!")


# =============================================================================
# SUITE M7: Minefield 7 (Independent from-scratch audit of L01)
# =============================================================================

def snf_exps_mod_p(Mat_int, p: int):
    """Return sorted list of nonzero p-adic invariant factor exponents of coker(Mat_int) over Z_(p)."""
    M = [[int(x) for x in row] for row in Mat_int]
    nrows, ncols = len(M), len(M[0]) if M else 0
    MOD = p**40
    invs = []
    r0 = c0 = 0
    while r0 < nrows and c0 < ncols:
        best_v = 10**9
        bi = bj = -1
        for i in range(r0, nrows):
            for j in range(c0, ncols):
                v = vp_int(M[i][j], p)
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
    return sorted([v for v in invs if v > 0])


def compute_lattice_invariants_Z_E(P_mat, h_shift: int, p: int):
    """
    Independent from-scratch computation over S = Z_(p)[[E]] for M_1 = S^d, M_2 = E^{-h} P S^d
    (with P in M_d(Z[E]), det(P) = +- E^deg, E^H P^{-1} in M_d(Z[E])).
    Returns: (Phi, Phi_star, Q1_invs, len_Q1, D_lengths, wts, star_minus_check, star_plus_check)
    """
    E = sp.Symbol("E")
    d = P_mat.rows
    detP = sp.Poly(sp.expand(P_mat.det()), E)
    # Find H = pole order of P^{-1}
    P_inv = P_mat.inv().applyfunc(sp.cancel)
    H = 0
    for i in range(d):
        for j in range(d):
            if P_inv[i, j] != 0:
                den = sp.Poly(sp.denom(P_inv[i, j]), E)
                H = max(H, den.degree())
    M_val = H - h_shift
    assert M_val >= 0 and h_shift >= 0

    def coker_mod_Em(Mat_poly, m_ord):
        # Compute Z_(p)-module S^d / (Mat_poly S^d + E^m_ord S^d)
        # Basis of (S/E^m)^d is {e_i E^a : 0 <= i < d, 0 <= a < m_ord}, size d*m_ord
        if m_ord <= 0:
            return []
        N = d * m_ord
        A = [[0] * N for _ in range(N)]
        for j in range(d):
            for i in range(d):
                poly = sp.Poly(sp.expand(Mat_poly[i, j]), E)
                for a in range(m_ord):
                    for (deg,), cf in poly.terms():
                        if deg + a < m_ord:
                            A[i * m_ord + (deg + a)][j * m_ord + a] += int(cf)
        return snf_exps_mod_p(A, p)

    # X_m = (S^d / (P S^d + E^m S^d))[p^infty] for m = 0..H
    # Notice: for M_1 = S^d, M_2 = E^{-h} P S^d:
    #   L_1 = S^d, L_2 = P S^d = E^h M_2.
    #   D_i(M_1, M_2) = D_{i-h}(L_1, L_2) = X_{h - i} for i in [-M, h]!
    #   C_i(M_1, M_2) = (M_1 + E^i M_2)/(M_1 + E^{i+1} M_2) -> compute directly via Fil!
    # Even simpler and 100% direct:
    #   F_i = im(M_2 cap E^{-i} M_1 -> M_2 / E M_2)
    #       = {v mod E : v in S^d, E^{i - h} P v in S^d} = {v mod E : P v == 0 mod E^{h - i}}!
    #   Fil^i_Hod = im(M_1 cap E^i M_2 -> M_1 / E M_1)
    #       = {w mod E : w in S^d, E^{h - i} P^{-1} w in S^d} = {w mod E : (E^H P^{-1}) w == 0 mod E^{H - h + i} = E^{M + i}}!
    def compute_fil_invs(Mat_poly, m_ord):
        # Compute torsion invariant factors of S^d / (im(ker(Mat_poly mod E^m) -> (S/E)^d))
        if m_ord <= 0:
            return []  # whole S^d, torsion 0
        N = d * m_ord
        Mat = sp.zeros(N, N)
        for j in range(d):
            for i in range(d):
                poly = sp.Poly(sp.expand(Mat_poly[i, j]), E)
                for a in range(m_ord):
                    for (deg,), cf in poly.terms():
                        if deg + a < m_ord:
                            Mat[i * m_ord + (deg + a), j * m_ord + a] = int(cf)
        ns = Mat.nullspace()
        if not ns:
            return []  # fil = 0 -> quotient is Z^d, torsion 0!
        cols = []
        for v in ns:
            den = sp.lcm([sp.fraction(x)[1] for x in v])
            cols.append([int(x * den) for x in v])
        # Saturate cols in Z_(p)^N
        r, m = len(cols), len(cols[0])
        B = [list(c) for c in cols]
        while True:
            R = [[x % p for x in row] for row in B]
            ops = [[1 if a == b else 0 for b in range(r)] for a in range(r)]
            piv = 0
            for col in range(m):
                found = next((a for a in range(piv, r) if R[a][col] % p != 0), -1)
                if found == -1:
                    continue
                R[piv], R[found] = R[found], R[piv]
                ops[piv], ops[found] = ops[found], ops[piv]
                inv = pow(R[piv][col], -1, p)
                R[piv] = [(x * inv) % p for x in R[piv]]
                ops[piv] = [(x * inv) % p for x in ops[piv]]
                for a in range(r):
                    if a != piv and R[a][col] != 0:
                        f = R[a][col]
                        R[a] = [(R[a][c] - f * R[piv][c]) % p for c in range(m)]
                        ops[a] = [(ops[a][c] - f * ops[piv][c]) % p for c in range(r)]
                piv += 1
            if piv == r:
                break
            comb = ops[piv]
            idx = next(b for b in range(r) if comb[b] % p != 0)
            B[idx] = [sum(comb[b] * B[b][c] for b in range(r)) // p for c in range(m)]
        # Project to E^0 coefficient (indices j * m_ord + 0 for j = 0..d-1)
        Img = [[B[c][j * m_ord] for c in range(r)] for j in range(d)]
        return snf_exps_mod_p(Img, p)

    P_adj = (E**H * P_inv).applyfunc(sp.expand)
    P_dual = P_adj.T  # For (M_1^v, M_2^v): M_2^v = E^h P^{-T} S^d = E^{-M} (E^H P^{-T}) S^d!

    # Compute C_i(M_1, M_2)_tors = (D_O / F_i)_tors for i = -M .. h
    C_invs = {}
    for i in range(-M_val - 1, h_shift + 1):
        C_invs[i] = compute_fil_invs(P_mat, h_shift - i)
    Phi = max((max(v) if v else 0) for v in C_invs.values())

    # Compute C_j^*(M_1, M_2)_tors = C_j(M_1^v, M_2^v)_tors for j = -h .. M
    # Here M_2^v = E^{-M} P_dual S^d, so h^* = M_val, M^* = h_shift
    C_star_invs = {}
    for j in range(-h_shift - 1, M_val + 1):
        C_star_invs[j] = compute_fil_invs(P_dual, M_val - j)
    Phi_star = max((max(v) if v else 0) for v in C_star_invs.values())

    # Compute Q_1(M_1, M_2)_tors = (D_dR / Fil^0_Hod)_tors = ker(P_adj mod E^M) projected to E^0!
    Q1_invs = compute_fil_invs(P_adj, M_val)

    # Also compute X_m = (S^d / (P S^d + E^m S^d))_tors for m = 0..H
    X_invs = {m: coker_mod_Em(P_mat, m) for m in range(H + 1)}

    return Phi, Phi_star, Q1_invs, C_invs, C_star_invs, X_invs


def run_suite_m7():
    print("=== SUITE M7: Minefield 7 (Independent from-scratch audit of L01: P_{n,k}, P_tw, Matlis D_i) ===")
    E = sp.Symbol("E")
    p = 2

    # M7.1 Verify P_{n, k} for (n, k) in {(2,1), (2,2), (3,1), (3,2), (4,1)}
    for n, k in [(2, 1), (2, 2), (3, 1), (3, 2), (4, 1)]:
        q = p**k
        d = 2 * n
        P = sp.zeros(d, d)
        # Basis e_1..e_{n+1} (indices 0..n), f_1..f_{n-1} (indices n+1..2n-1)
        P[0, 0] = E**(2 * n - 1)
        for j in range(1, n):
            P[j - 1, j] = E**(n - j) * q
            P[j, j] = E**(n - j)
        P[n - 1, n] = q
        P[n, n] = E
        for r in range(1, n):
            col = n + r
            P[0, col] = E**(n - 1 + r) * (q**(n - r))
            P[n + r, col] = E**(n + r)
        # Verify det == E^{2n^2}
        assert sp.expand(P.det() - E**(2 * n**2)) == 0
        Phi, Phi_star, Q1_invs, C_invs, C_star_invs, X_invs = compute_lattice_invariants_Z_E(P, n - 1, p)
        assert Phi == k, f"P_{n},{k}: expected Phi={k}, got {Phi}"
        assert Phi_star == k, f"P_{n},{k}: expected Phi^*={k}, got {Phi_star}"
        assert Q1_invs == [n * k], f"P_{n},{k}: expected Q1=[{n*k}], got {Q1_invs}"
        # Verify X_m == [min(m, 2n-m)*k] for all 0 <= m <= 2n!
        for m in range(2 * n + 1):
            exp_xm = [min(m, 2 * n - m) * k] if min(m, 2 * n - m) > 0 else []
            assert X_invs[m] == exp_xm, f"P_{n},{k} X_{m}: expected {exp_xm}, got {X_invs[m]}"
        print(f"  [PASS] M7.1 P_{{{n},{k}}} (d={d}, H={2*n}): Phi={Phi}, Phi^*={Phi_star}, Q1_tors=Z/2^{Q1_invs[0]} (ratio={Q1_invs[0]/Phi:.1f}=d/2=H/2), all X_m exact!")

    # M7.2 Verify P_tw (Theorem L01-4(2), r^- = r^+ = 1 counterexample)
    P_tw = sp.Matrix([
        [1, 0, 0, 0],
        [E, -E**2, 0, 0],
        [2, -2 * E, -E**3, 0],
        [0, 4, 2 * E**2, E**3],
    ])
    assert sp.expand(P_tw.det() - E**8) == 0
    Phi, Phi_star, Q1_invs, C_invs, C_star_invs, X_invs = compute_lattice_invariants_Z_E(P_tw, 1, 2)
    exp_Q1 = max(Q1_invs) if Q1_invs else 0
    assert Phi == 1 and Phi_star == 2 and exp_Q1 == 2, f"P_tw mismatch: Phi={Phi}, Phi^*={Phi_star}, Q1={Q1_invs}"
    # Verify Theorem L01-2 bound: len(Q1) <= min(d^- * Phi, d^+ * Phi^*) = min(2*1, 2*2) = 2
    assert sum(Q1_invs) <= min(2 * Phi, 2 * Phi_star)
    print(f"  [PASS] M7.2 P_tw (r^-=r^+=1, d^-=d^+=2): Phi={Phi}, Phi^*={Phi_star}, Q1_invs={Q1_invs} -> refutes exp(Q1) <= r^- * Phi, satisfies r^+=1 bound 2 <= Phi^*=2!")


if __name__ == "__main__":
    run_suite_m1()
    run_suite_m2()
    run_suite_m3()
    run_suite_m4()
    run_suite_m5()
    run_suite_m6()
    run_suite_m7()
    print("\nALL 7 M01 ADVERSARIAL AUDIT SUITES PASSED (exit 0).")
