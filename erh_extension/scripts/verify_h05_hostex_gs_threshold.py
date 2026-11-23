#!/usr/bin/env python3
"""
Wave-10 H05 Exact Symbolic & Numerical Verification Script
File: erh_research/scripts/verify_h05_hostex_gs_threshold.py

Verifies all algebraic, combinatorial, analytic, and number-theoretic
calculations in H05_hostex_weakest_threshold_and_gs_tower.md:
  Suite 1: Exact Lean 4.33.1 Krull-dimension thresholds (HostEx & ChCore),
           decoupled rank budgets, and finite q-group exponent vs order check.
  Suite 2: Explicit unramified totally real Golod-Shafarevich q=3 class field
           towers over Q, Q(sqrt(5)), and F^+_725 (unconstrained & T-split).
  Suite 3: Exact Louboutin (2000) + Zimmert (1981) unconditional class-number
           slope constants, Case 2(a) crossover primes l_0, and Schinzel (1973)
           vs naive Wieferich norm bound crossover.
  Suite 4: Exact quantitative failure in Case 2(b) (full class group, single
           eigenspace product formula, and Ellenberg-Venkatesh Lemma 2.3 cutoff).
  Suite 5: Exact cyclotomic & real-quadratic checks on L(0, omega_l^{-1}) and
           smoothing factor (1 - omega_l^{-1}(c) Nm(c)) for small primes l.
  Suite 6: Positive-proportion non-vanishing thresholds on Z_q-cyclotomic towers
           (with vs without bounded-multiplicity hypothesis BM(M)).

Note: Finite numerical/symbolic instances cross-verify general theorems and
exact constants; finite checks do not substitute for general proofs.
"""

import math
import sys
from fractions import Fraction
import sympy as sp


def banner(title: str) -> None:
    print("\n" + "=" * 78)
    print(title)
    print("=" * 78)


# ---------------------------------------------------------------------------
# Suite 1: Exact Lean Thresholds (HostEx & ChCore) and q-Group Exponent Check
# ---------------------------------------------------------------------------
def suite1_lean_thresholds() -> None:
    banner("Suite 1: Exact Lean 4.33.1 Thresholds (HostEx & ChCore)")

    # 1A. Symbolic verification of CharpolyCoeffsInSubalgebra.lean:63-84 (l51)
    # and KrullDimLtOfNotLeTriangular.lean:44-58
    d, r_h1, r_b1, r_b1p, C0 = sp.symbols("d r_h1 r_b1 r_b1p C0", integer=True, nonnegative=True)

    # Number of parameters t in CharpolyCoeffsInSubalgebra.lean:63:
    # Unit (varpi) + Fin(1 + r_h1 + d) (s from ab_plus & ab_minus) + (n - 2)*d (s' for w(i)=0)
    for n in (2, 3):
        card_t = 1 + (1 + r_h1 + d) + (n - 2) * d
        fib_dim_exact = r_b1p if n == 2 else (r_b1 + r_b1p)
        dim_triM_exact = sp.simplify(card_t + fib_dim_exact)
        # Need dim_triM_exact <= n*d - 1  <=>  dim_triM_exact < n*d
        gap_exact = sp.simplify(n * d - dim_triM_exact)
        # Unmodified code sets r_h1 = r_b1 = r_b1p = C0 and adds +5 slack in l51:
        dim_triM_lean = (n - 1) * d + 2 + (3 * C0 + 5)
        gap_lean = sp.simplify(n * d - dim_triM_lean)
        print(f"  HostEx n={n}: card(t) = {card_t}, fib_dim_exact = {fib_dim_exact}")
        print(f"    Exact sharp condition (dim < n*d): {dim_triM_exact} < {n*d}  <=>  {sp.simplify(n*d - gap_exact - (n-1)*d)} < d")
        print(f"    Unmodified Lean Big (l51 + 5 slack): {dim_triM_lean} < {n*d}  <=>  {sp.simplify(dim_triM_lean - (n-1)*d)} < d")
        if n == 2:
            assert sp.simplify(gap_exact - (d - (r_h1 + r_b1p + 2))) == 0
        else:
            assert sp.simplify(gap_exact - (d - (r_h1 + r_b1 + r_b1p + 2))) == 0
        assert sp.simplify(gap_lean - (d - (3 * C0 + 7))) == 0

    # 1B. Check l52 (TameInertiaCondition.lean:258 & KrullDimLtOfNotLeTriangular.lean:55-58)
    # dim(L.R / P) + dv(v) <= n*d + 5  ==>  dim(L.R / P) <= n*d - 1  iff  5 < dv(v)
    dv = sp.Symbol("dv", integer=True, positive=True)
    for n in (2, 3):
        # Need (n*d + 5) <= (n*d - 1) + dv  <=>  6 <= dv  <=>  5 < dv
        assert sp.simplify((n * d + 5) - ((n * d - 1) + dv)) == 6 - dv
    print("  HostEx l52 check: dim + dv <= n*d + 5 gives dim <= n*d - 1 iff dv >= 6 (5 < dv), ZERO g_l term!")

    # 1C. Check ChCore (ChCore.lean:31-32, 117 & ChCore_ZqTower.lean:277-295)
    r, g, gL, dMin = sp.symbols("r g gL dMin", integer=True, nonnegative=True)
    N = 2 * d + 1 - 2 * gL
    tan_bound = d + 10 * r + 5 * g + 6 * gL + 15
    # hN1: tan_bound + 1 < N  <=>  10*r + 5*g + 8*gL + 15 < d
    hN1_lhs = sp.simplify((tan_bound + 1) - (N - d))
    assert sp.simplify(hN1_lhs - (10 * r + 5 * g + 8 * gL + 15)) == 0
    # hN2: 2*d + 1 + (2 + 4*gL) < N + dMin  <=>  2 + 6*gL < dMin
    hN2_diff = sp.simplify((2 * d + 1 + (2 + 4 * gL)) - (N + dMin))
    assert sp.simplify(hN2_diff - (2 + 6 * gL - dMin)) == 0
    print("  ChCore LinDepthOK verified symbolically:")
    print("    (hN1): 10*r + 5*g + 8*gL + 15 < d   (slope threshold c0 = 1/10 unified, 1 decoupled over 10 roots)")
    print("    (hN2): 2 + 6*gL < dMin              (forces dMin > sqrt(6*d) since gL * dMin <= d)")

    # 1D. Check semisimple q-adic analytic quotient SL_2(Z_q) / Gamma(q^{k+1}):
    # |P_k| = q^{3k}, exp(P_k) = q^k (q odd), so exp(P_k)^2 / |P_k| = q^{-k} -> 0
    for q in (3, 5):
        for k in (1, 2, 5, 10):
            order_P = q ** (3 * k)
            exp_P = q ** k
            assert exp_P ** 2 < order_P
    print("  q-group (hN2) check: for Gamma(q)/Gamma(q^{k+1}) in SL_2(Z_q), exp^2 = |P|^{2/3} << |P|.")
    print("  [PASS] Suite 1 passed.")


# ---------------------------------------------------------------------------
# Suite 2: Explicit Unramified Totally Real Golod-Shafarevich q=3 Towers
# ---------------------------------------------------------------------------
def is_prime(n: int) -> bool:
    return sp.isprime(n)


def splits_completely_F725(p: int) -> bool:
    """
    Check if rational prime p splits completely in F^+_725, defined by
    f(x) = x^4 - x^3 - 3*x^2 + x + 1 (disc = 725 = 5^2 * 29, D_4 quartic).
    """
    if p in (5, 29):
        return False
    x = sp.Symbol("x")
    poly = sp.Poly(x**4 - x**3 - 3 * x**2 + x + 1, x, modulus=p)
    facs = poly.factor_list()[1]
    return len(facs) == 4 and all(f.degree() == 1 and e == 1 for f, e in facs)


def splits_completely_Qsqrt5(p: int) -> bool:
    if p == 5:
        return False
    return sp.legendre_symbol(5, p) == 1


def suite2_gs_towers() -> dict:
    banner("Suite 2: Explicit Unramified Totally Real Golod-Shafarevich q=3 Towers")

    # Verify discriminant of f(x) = x^4 - x^3 - 3x^2 + x + 1 is 725
    x = sp.Symbol("x")
    f725 = sp.Poly(x**4 - x**3 - 3 * x**2 + x + 1, x)
    disc725 = int(sp.discriminant(f725))
    assert disc725 == 725, f"Expected 725, got {disc725}"
    # Verify all 4 roots are real (totally real)
    roots725 = [complex(r) for r in sp.nroots(f725)]
    assert all(abs(r.imag) < 1e-10 for r in roots725)
    print(f"  Verified F^+_725: f(x) = x^4 - x^3 - 3x^2 + x + 1, disc = {disc725}, totally real.")

    q = 3
    results = {}
    cases = [
        ("Q", 1, 1.0, lambda p: True, {2, 3}),
        ("Q(sqrt(5))", 2, math.sqrt(5.0), splits_completely_Qsqrt5, {2, 3, 5}),
        ("F^+_725", 4, 725.0 ** 0.25, splits_completely_F725, {2, 3, 5, 29}),
    ]

    for name, n0, rd_K0, split_fn, bad_set in cases:
        d0 = q * n0
        # Need t - 1 >= 2 + 2*sqrt(d0)  <=>  t >= ceil(3 + 2*sqrt(d0))
        t_min = math.ceil(3.0 + 2.0 * math.sqrt(d0))
        # Verify exact Golod-Shafarevich-Vinberg inequality:
        # d(G) >= t_min - 1, r(G) <= d(G) + d0 - 1, need r(G) <= d(G)^2 / 4
        dG = t_min - 1
        rG_ub = dG + d0 - 1
        assert 4 * rG_ub <= dG * dG, f"GS failed for {name}: 4*{rG_ub} > {dG}^2"
        # Check t_min - 1 would fail if strictly smaller
        if dG - 1 >= 0:
            assert 4 * ((dG - 1) + d0 - 1) > (dG - 1) ** 2

        # Collect first t_min primes p == 1 (mod 3) outside bad_set splitting completely in K0
        primes = []
        p = 7
        while len(primes) < t_min:
            if is_prime(p) and p % q == 1 and p not in bad_set and split_fn(p):
                primes.append(p)
            p += 2

        # Root discriminant of F0^+ = K0 * E_q:
        # Since gcd(disc(K0), prod p_i) = 1 and E_q has conductor prod p_i (degree q=3,
        # conductor-discriminant formula gives |D_{E_q}| = (prod p_i)^{q-1} = (prod p_i)^2):
        # rd(F0^+) = rd(K0) * (prod p_i)^{(q-1)/q} = rd(K0) * (prod p_i)^{2/3}
        log_prod_p = sum(math.log(pr) for pr in primes)
        log_R0 = math.log(rd_K0) + ((q - 1) / q) * log_prod_p
        R0 = math.exp(log_R0)

        print(f"\n  Base field {name} (n0={n0}, rd(K0)={rd_K0:.4f}):")
        print(f"    d0 = 3*n0 = {d0}, min ramified primes t = {t_min} (d(G) >= {dG}, r(G) <= {rG_ub}, d(G)^2/4 = {dG**2/4:.2f})")
        print(f"    Smallest primes p == 1 (mod 3) splitting in {name}: {primes}")
        print(f"    log(R0) = {log_R0:.4f}, R0 = rd(F0^+) = {R0:.3e}")

        # Also check T-split tower with |T| = d0 (worst case: every place above l splits completely in F0^+)
        T_size = d0
        t_T = T_size + math.ceil(3.0 + 2.0 * math.sqrt(d0 + T_size))
        dG_T = t_T - 1 - T_size
        rG_T_ub = dG_T + d0 - 1 + T_size
        assert 4 * rG_T_ub <= dG_T * dG_T
        print(f"    T-split (|T|={T_size}): t_T = {t_T}, d(G_T) >= {dG_T}, r(G_T) <= {rG_T_ub}, d(G_T)^2/4 = {dG_T**2/4:.2f}")

        results[name] = {
            "n0": n0,
            "d0": d0,
            "t_min": t_min,
            "primes": primes,
            "log_R0": log_R0,
            "R0": R0,
        }

    print("\n  [PASS] Suite 2 passed.")
    return results


# ---------------------------------------------------------------------------
# Suite 3: Louboutin (2000) + Zimmert (1981) Constants & Case 2(a) / Schinzel
# ---------------------------------------------------------------------------
def suite3_louboutin_zimmert_case2a(gs_results: dict) -> None:
    banner("Suite 3: Louboutin (2000) + Zimmert (1981) Bounds, Case 2(a) & Schinzel")

    # Exact constants from analytic class number formula + Louboutin (2000) + Zimmert (1981):
    # h_K R_K = w_K / (2^{r1} (2 pi)^{r2}) * |D_K|^{1/2} * Res_{s=1} zeta_K(s)
    # Louboutin (2000): Res_{s=1} zeta_K(s) <= (e * log|D_K| / (2(N-1)))^{N-1}
    #   Asymptotically per degree: log(e/2) + log(log R) = 1 - log(2) + log(log R)
    # Zimmert (1981): 2 R_K / w_K >= 0.04 * exp(0.46 r1 + 0.1 r2)
    #   Per degree: (0.46 r1 + 0.1 r2) / N
    # Totally real (r1 = N, r2 = 0):
    c_real = 1.0 - math.log(2.0) - math.log(2.0) - 0.46
    # Totally complex (r1 = 0, r2 = N/2):
    c_cm = 1.0 - math.log(2.0) - 0.5 * math.log(2.0 * math.pi) - 0.05
    print(f"  Louboutin+Zimmert additive constant (totally real):    {c_real:.6f}")
    print(f"  Louboutin+Zimmert additive constant (totally complex): {c_cm:.6f}")
    assert abs(c_real - (-0.84629436)) < 1e-5
    assert abs(c_cm - (-0.66208046)) < 1e-5

    # Case 2(a): Compute exact threshold l_0 where Louboutin-Zimmert bound on
    # rk_l(Cl(L_{tame, n})) / d_n drops below target slopes 1/3, 1/6, 1/10
    # Here L_{tame, 0} = F_0^+ * K_eta * K_psi with K_eta = Q(i) (rd = 2),
    # and tame character psi of order m_psi, conductor N_psi (rd(K_psi) <= N_psi).
    print("\n  Case 2(a) (omega_l^e = 1): unconditional threshold log10(l_0) for b1p/b1/Cl(F_n^+):")
    for base_name in ("Q(sqrt(5))", "F^+_725"):
        log_R0 = gs_results[base_name]["log_R0"]
        for label, M_tame, log_N_extra in [
            ("F_n^+ itself (Cl(F_n^+))", 1, 0.0),
            ("L_tame = F_n^+(i), psi=1 (M=2)", 2, math.log(2.0)),
            ("L_tame = F_n^+(i)*K_41, deg 2 (M=4)", 4, math.log(2.0) + 0.5 * math.log(41.0)),
        ]:
            log_R = log_R0 + log_N_extra
            c_const = c_real if M_tame == 1 else c_cm
            # Upper bound on limsup (log_l h(L_n)) / d_n is M_tame * (0.5*log_R + log(log_R) + c_const) / log(l)
            num = M_tame * (0.5 * log_R + math.log(log_R) + c_const)
            l0_third = num / (1.0 / 3.0) / math.log(10.0)   # log10(l_0) for < 1/3
            l0_tenth = num / (1.0 / 10.0) / math.log(10.0)  # log10(l_0) for < 1/10
            print(f"    {base_name:10s} | {label:36s}: num={num:7.2f}, log10(l0[<1/3])={l0_third:6.1f}, log10(l0[<1/10])={l0_tenth:6.1f}")

    # Schinzel (1973) totally real height lower bound vs naive Wieferich norm bound:
    # h(eps) >= (1/2) log((1+sqrt(5))/2) = 0.2406059125...
    # Naive norm bound for eps^{l-1} == 1 (mod l^2): h(eps) >= (2*log(l) - log(2)) / (l - 1)
    h_schinzel = 0.5 * math.log((1.0 + math.sqrt(5.0)) / 2.0)
    print(f"\n  Schinzel (1973) totally real height floor: h_S = {h_schinzel:.6f}")
    first_below = None
    for l in [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41]:
        h_wief = (2.0 * math.log(l) - math.log(2.0)) / (l - 1)
        status = "< h_S (VACUOUS)" if h_wief < h_schinzel else ">= h_S"
        if h_wief < h_schinzel and first_below is None:
            first_below = l
        print(f"    l={l:2d}: naive Wieferich bound (2*log l - log 2)/(l-1) = {h_wief:.6f}  [{status}]")
    print(f"  Exact crossover: naive Wieferich bound becomes strictly weaker than Schinzel at l >= {first_below}!")
    assert first_below == 29
    print("  [PASS] Suite 3 passed.")


# ---------------------------------------------------------------------------
# Suite 4: Exact Quantitative Failure in Case 2(b) & Ellenberg-Venkatesh Cutoff
# ---------------------------------------------------------------------------
def suite4_case2b_obstruction() -> None:
    banner("Suite 4: Case 2(b) (omega_l^e != 1) Obstruction & Ellenberg-Venkatesh Cutoff")

    # For Count I weights e and primes l > 2*e + 1 (so (l-1) nmid 2e):
    print("  Table: Full-class-group Minkowski slope vs Single-eigenspace Product Formula slope:")
    print(f"  {'l':>6s} {'e':>3s} {'m1':>5s} {'m2':>5s} {'phi(m2)':>7s} {'FullCl(M=2)':>12s} {'SingleEig':>10s} {'h1_Full':>9s} {'h1_Prod':>9s} {'EV_X_inf':>9s}")
    R_tame = 1000.0  # optimistic Martinet-scale totally real rd
    for l in (5, 7, 11, 13, 17, 29, 37, 101, 1009, 10007):
        e = 1 if l > 3 else 1
        m1 = (l - 1) // math.gcd(e, l - 1)
        m2 = (l - 1) // math.gcd(2 * e, l - 1)
        phi_m2 = int(sp.totient(m2))
        phi_lm1 = int(sp.totient(l - 1))
        M_tame = 2  # minimal K_eta = Q(i), psi = 1
        full_cl_slope = (m1 - 1) * M_tame / 2.0
        single_eig_slope = phi_m2 / 2.0
        h1_full_slope = (l - 2) / 2.0
        h1_prod_slope = phi_lm1 / 2.0
        # Ellenberg-Venkatesh Lemma 2.3 norm cutoff X_inf = rd(L_Psi)^{1/(2l)}
        rd_L = R_tame * (l ** (1.0 - 1.0 / m1))
        X_inf = rd_L ** (1.0 / (2.0 * l))
        print(f"  {l:6d} {e:3d} {m1:5d} {m2:5d} {phi_m2:7d} {full_cl_slope:12.2f} {single_eig_slope:10.2f} {h1_full_slope:9.2f} {h1_prod_slope:9.2f} {X_inf:9.4f}")
        assert full_cl_slope >= 1.0
        assert h1_full_slope >= 1.5
        if l >= 13:
            assert X_inf < 2.0, f"Expected EV cutoff < 2 at l={l}, got {X_inf}"

    # Check the absolute best Case 2(b) subcase: m1 = 2 (quadratic omega_l^e, e.g. e = (l-1)/2)
    # Then m2 = 1 (b1p is unramified!), but b1 has m1 = 2:
    # Full class group of F_n^+(i, sqrt(l*)) has M_tame = 2, m1 = 2 => (2-1)*2/2 = 1.0
    # Single eigenspace of b1_odd (order m1 = 2, phi(2) = 1) has slope 1/2 > 1/3 (fails unmodified Big!)
    # AND h1 STILL has full slope (l-2)/2 and product-formula slope phi(l-1)/2 -> inf!
    print("\n  Best Case 2(b) subcase (m1=2, e=(l-1)/2, omega_l^e quadratic):")
    print("    b1p (m2=1): unramified -> slope -> 0 as l -> inf")
    print("    b1_odd (m1=2, phi(2)=1): single-eigenspace product formula gives 1/2 > 1/3 (fails unmodified Big)")
    print("    b1_even (m1=2): F_n^+(sqrt(l*)) Minkowski slope gives 1/2; sum b1_even + b1_odd = 1.0 (fails < 1)")
    print("    h1 (omega_l): ALWAYS has full slope (l-2)/2 and product-formula slope phi(l-1)/2 -> inf!")

    # Verify Ellenberg-Venkatesh saving delta(l) = 1/(2l) even if degree-independent:
    for l in (5, 7, 11, 13, 101):
        assert 0.5 - 1.0 / (2.0 * l) > 1.0 / 3.0
    print("  Hypothetical degree-independent EV saving: 1/2 - 1/(2l) >= 0.4 > 1/3 for all l >= 5!")
    print("  [PASS] Suite 4 passed.")


# ---------------------------------------------------------------------------
# Suite 5: Exact Checks on L_Q(0, omega_l^{-1}) and L_{Q(sqrt(5))}(0, omega_l^{-1} o N)
# ---------------------------------------------------------------------------
def teichmuller_mod_l2(a: int, l: int) -> int:
    """Return the unique integer w in [0, l^2-1] with w == a (mod l) and w^{l-1} == 1 (mod l^2)."""
    if a % l == 0:
        return 0
    return pow(a, l, l * l)


def suite5_exact_omega_L_values() -> None:
    banner("Suite 5: Exact Checks on L_Q(0, omega_l^{-1}) & L_{Q(sqrt(5))}(0, omega_l^{-1} o N)")

    # 5A. Over Q: verify B_{1, omega_l^{-1}} = (1/l) sum_{a=1}^{l-1} a * omega_l(a)^{-1}
    # In Z_l, omega_l(a) == a^l (mod l^2), so omega_l(a)^{-1} == a^{l^2 - 2l} = (a^l)^{-1} (mod l^2).
    # Multiply by l: sum_{a=1}^{l-1} a * omega_l(a)^{-1} == sum_{a=1}^{l-1} 1 = l - 1 == -1 (mod l)!
    # Hence v_l(L_Q(0, omega_l^{-1})) = -1 (pole of order 1), and for any c with c^{l-1} != 1 (mod l^2),
    # v_l((1 - omega_l(c)^{-1} * c) * L_Q(0, omega_l^{-1})) = 1 + (-1) = 0 (UNIT => Herbrand: Cl(Q(zeta_l))[l]^(omega) = 0)!
    print("  5A. Exact p-adic check over Q (mod l^2):")
    for l in (5, 7, 11, 13, 17, 19, 23):
        l2 = l * l
        s_num = 0
        for a in range(1, l):
            w = teichmuller_mod_l2(a, l)
            w_inv = pow(w, -1, l2)
            s_num = (s_num + a * w_inv) % l2
        # L_Q(0, omega^{-1}) = -B_{1, omega^{-1}} = -s_num / l (mod l)
        assert s_num % l == l - 1, f"Expected -1 mod {l}, got {s_num % l}"
        # Find smallest prime c != l with c^{l-1} != 1 (mod l^2)
        c = 2
        while c == l or pow(c, l - 1, l2) == 1:
            c = sp.nextprime(c)
        wc_inv = pow(teichmuller_mod_l2(c, l), -1, l2)
        smooth = (1 - wc_inv * c) % l2
        assert smooth % l == 0 and smooth != 0  # exact valuation 1!
        # Product smooth * (-s_num / l) mod l:
        prod_mod_l = ((smooth // l) * (-s_num)) % l
        assert prod_mod_l != 0
        print(f"    l={l:2d}: l*B_{{1,w^-1}} == {s_num % l - l:2d} (mod l), smooth c={c} has v_l(1-w^-1(c)c)=1, unit mod l = {prod_mod_l}")

    # 5B. Exact algebraic norm of L_{Q(sqrt(5))}(0, omega_l^{-1} o N) for l = 7 (prime inert in Q(sqrt(5)), l != 5)
    # and l = 11 (prime split in Q(sqrt(5)), l != 5)!
    # Using Shintani's exact formula on K0 = Q(sqrt(5)) with fundamental totally positive unit eps_+ = (3 + sqrt(5))/2:
    # For any character chi of conductor f*O_{K0} (f = l rational prime != 5) with chi(-1) = +1 (totally odd on K0!):
    # Wait: omega_l(-1) = -1, so (omega_l o N)(-1) = omega_l((-1)^2) = +1!
    # Check signature of chi = omega_l^{-1} o N at the two real places of K0:
    # For x in K0, N(x) = sigma_1(x) * sigma_2(x), and for a totally odd idele character on K0,
    # chi_fin(u) * sgn(N(u)) = 1 for all units u in O_{K0}^x!
    # CHECK FUNDAMENTAL UNIT omega_0 = (1+sqrt(5))/2 of K0: N(omega_0) = -1!
    # Wait: (omega_l^{-1} o N)(omega_0) = omega_l^{-1}(-1) = -1 = sgn(N(omega_0))!
    # SO omega_l^{-1} o N IS AUTOMATICALLY TOTALLY ODD ON Q(sqrt(5))!
    # Check Shintani formula for conductor f = l (zero row/col sums? Wait: N(a + b*eps_+) = a^2 + 3ab + b^2!):
    # Check row/col sum of omega_l^{-1}(a^2 + 3ab + b^2) over a = 0..l-1:
    # For fixed b != 0, a^2 + 3ab + b^2 = (a + 3b/2)^2 - 5b^2/4 takes BOTH QR and NQR values,
    # so row/col sums are NOT zero — we must include the FULL Shintani B_2 + B_1*B_1 + boundary B_1 formula!
    print("\n  5B. Exact Shintani computation of L_{Q(sqrt(5))}(0, omega_l^{-1} o N) in Q(zeta_{l-1}):")
    for l in (7, 11):
        # Compute L_{K0}(0, chi) where chi(x) = omega_l^{-1}(N(x)) for x = a + b*eps_+ (eps_+ = (3+sqrt(5))/2)
        # Note N(a + b*eps_+) = a^2 + 3*a*b + b^2, and Tr(eps_+) = 3, eps_+ + eps_+^{-1} = 3.
        # Full Shintani formula for cone C_open = {x1 + x2*eps_+ : x1, x2 > 0} and C_ray = {x1 : x1 > 0}:
        # For a totally odd character chi mod f (here f = l), with chi(eps_+) = omega_l^{-1}(+1) = +1:
        # L_{K0}(0, chi) = sum_{1<=a,b<=f} chi(a + b*eps_+) * [ B_1(a/f)*B_1(b/f) + (Tr(eps_+)/2)*(B_2(a/f) + B_2(b/f))/2 ]
        # Wait: let's recall Shintani's exact 2D formula for cone(v1, v2) with v1 = 1, v2 = eps_+:
        #   zeta_2(0; x1, x2; 1, eps_+) = B_1(x1)*B_1(x2) + (1/4)*(eps_+ + eps_+^{-1})*(B_2(x1) + B_2(x2))?
        # Let's check the EXACT coefficient of B_2 via SymPy residue of (e^{x1 t1} / (e^{t1}-1)) * (e^{x2 t2} / (e^{t2}-1))!
        # For v1 = (1, 1), v2 = (e1, e2) with e1*e2 = 1, e1 + e2 = 3:
        # Shintani (1976) Prop. 1:
        #   Z(0; x1, x2) = (1/2) * [ coeff of t^0 in (e^{-x1 t}/(1-e^{-t})) * (e^{-x2 e1 t}/(1-e^{-e1 t}))
        #                           + coeff of t^0 in (e^{-x1 t}/(1-e^{-t})) * (e^{-x2 e2 t}/(1-e^{-e2 t})) ]
        # Compute that coefficient symbolically with SymPy (ZERO guessing!!):
        t, x1s, x2s, e1s, e2s = sp.symbols("t x1 x2 e1 e2")
        # Use Bernoulli generating function: t*e^{x*t}/(e^t - 1) = sum B_n(x) t^n / n!
        # Note e^{-x*t}/(1 - e^{-t}) = e^{(1-x)*t}/(e^t - 1) = (1/t) * sum B_n(1-x) t^n / n!
        # Wait: for x in (0, 1], sum_{m>=0} e^{-(m+x)t} = e^{-x t}/(1 - e^{-t}) = (1/t) * [1 + B_1(1-x) t + B_2(1-x) t^2/2 + ...]
        # Notice B_1(1-x) = -B_1(x) and B_2(1-x) = B_2(x)!
        # So e^{-x1 t}/(1-e^{-t}) * e^{-x2 e t}/(1-e^{-e t})
        #   = (1/(e*t^2)) * [1 - B_1(x1) t + B_2(x1) t^2/2] * [1 - B_1(x2) e t + B_2(x2) e^2 t^2/2]
        # Coeff of t^0 is: (1/e) * [ B_2(x1)/2 + e*B_1(x1)*B_1(x2) + e^2*B_2(x2)/2 ]
        #                = B_1(x1)*B_1(x2) + (1/(2e))*B_2(x1) + (e/2)*B_2(x2)!
        # Average over e = e1 and e = e2 (where e1 + e2 = 3 and 1/e1 + 1/e2 = e2 + e1 = 3!):
        #   Z_open(0; x1, x2) = B_1(x1)*B_1(x2) + (3/4)*(B_2(x1) + B_2(x2))!
        # And for the 1D ray C_ray = {a > 0}:
        #   Z_ray(0; x1) = coeff of t^0 in e^{-x1 t}/(1 - e^{-t}) = -B_1(x1)!
        #Wait: check sign on C_open vs C_ray! For zeta_Q(s) = sum_{n>=1} n^{-s}, at s=0,
        # sum_{a=1}^f chi(a) * (-B_1(a/f)) = -B_{1, chi} = L_Q(0, chi)!
        # Check with F^+_725? Better: check directly on l = 7 against L_Q(0, omega_7^{-1}) * L_Q(0, omega_7^{-1} * chi_5)!!
        # OH!! BECAUSE omega_l^{-1} o N_{K0/Q} FACTORS AS A PRODUCT OF TWO DIRICHLET L-FUNCTIONS!!
        # L_{K0}(s, omega_l^{-1} o N) = L_Q(s, omega_l^{-1}) * L_Q(s, omega_l^{-1} * chi_5)!!
        # THAT'S AN EXACT IDENTITY WE CAN CHECK IN 2 LINES!!
        w_prim = sp.exp(2 * sp.pi * sp.I / (l - 1))
        g_prim = int(sp.primitive_root(l))
        # Discrete log base g_prim mod l
        dlog = {}
        cur = 1
        for k in range(l - 1):
            dlog[cur] = k
            cur = (cur * g_prim) % l

        # Exact polynomial in z = zeta_{l-1} modulo Phi_{l-1}(z):
        z = sp.Symbol("z")
        phi_poly = sp.Poly(sp.cyclotomic_poly(l - 1, z), z)

        def chi_val(n: int):
            r = n % l
            if r == 0:
                return sp.Integer(0)
            # omega_l^{-1}(r) represented by z^{-dlog[r] mod (l-1)}
            return z ** ((-dlog[r]) % (l - 1))

        # Factor 1: L_Q(0, omega_l^{-1}) = -(1/l) sum_{a=1}^{l-1} a * chi_val(a)
        L1 = sp.rem(sp.Poly(-sum(a * chi_val(a) for a in range(1, l)) / sp.Integer(l), z), phi_poly).as_expr()
        # Factor 2: L_Q(0, omega_l^{-1} * chi_5) = -(1/(5l)) sum_{a=1}^{5l-1} a * chi_val(a) * legendre(a, 5)
        L2 = sp.rem(
            sp.Poly(-sum(a * chi_val(a) * sp.legendre_symbol(a, 5) for a in range(1, 5 * l)) / sp.Integer(5 * l), z),
            phi_poly,
        ).as_expr()
        L_K0 = sp.rem(sp.Poly(sp.expand(L1 * L2), z), phi_poly).as_expr()

        # Cross-check against Shintani formula directly!
        def B1(u: Fraction) -> Fraction:
            return u - Fraction(1, 2)

        def B2(u: Fraction) -> Fraction:
            return u * u - u + Fraction(1, 6)

        S_open = sp.Integer(0)
        for a in range(1, l + 1):
            xa = Fraction(a, l)
            for b in range(1, l + 1):
                xb = Fraction(b, l)
                norm_ab = a * a + 3 * a * b + b * b
                cv = chi_val(norm_ab)
                if cv != 0:
                    wt = B1(xa) * B1(xb) + Fraction(3, 4) * (B2(xa) + B2(xb))
                    S_open += sp.Rational(wt.numerator, wt.denominator) * cv
        # Ray contribution: x = a (b=0), N(a) = a^2, chi(a^2) = omega_l^{-2}(a) (EVEN! -> sum_{a=1}^l (-B1(a/l))*chi(a^2) = 0!)
        S_ray = sum(
            sp.Rational((-B1(Fraction(a, l))).numerator, (-B1(Fraction(a, l))).denominator) * chi_val(a * a)
            for a in range(1, l + 1)
        )
        L_shintani = sp.rem(sp.Poly(sp.expand(S_open + S_ray), z), phi_poly).as_expr()
        assert sp.simplify(L_shintani - L_K0) == 0, f"Shintani mismatch at l={l}: {L_shintani} vs {L_K0}"

        # Compute exact rational norm of l * L_{K0}(0, omega_l^{-1} o N) (clearing the 1/l pole from L1!)
        # Note: L2 is integral (since omega_l^{-1}*chi_5 is ramified at 5 != l), so l * L_K0 is an ALGEBRAIC INTEGER!
        int_expr = sp.expand(l * L_K0)
        poly_int = sp.Poly(int_expr, z)
        assert all(c.is_integer for c in poly_int.all_coeffs()), f"Expected algebraic integer l*L_K0 at l={l}"
        norm_val = int(sp.resultant(phi_poly, poly_int, z))
        v_l_norm = sp.multiplicity(l, abs(norm_val))
        # Evaluate l * L_K0(0) mod P where P corresponds to z == g_prim (mod l)
        # (since chi_val(r) = z^{-dlog[r]}, evaluating at z = g_prim gives omega_l^{-1}(r) mod l!)
        val_at_P = int(poly_int.eval(g_prim)) % l
        leg5 = int(sp.legendre_symbol(l, 5))
        print(f"    l={l:2d} (chi_5(l)={leg5:+d}): Shintani == L1*L2 EXACT! "
              f"l*L_K0(0) = {int_expr}, Nm(l*L_K0) = {norm_val}, v_l(Nm) = {v_l_norm}, (l*L_K0 mod P) = {val_at_P}")

    print("  [PASS] Suite 5 passed.")


# ---------------------------------------------------------------------------
# Suite 6: Positive-Proportion Non-Vanishing Thresholds on Z_q-Towers
# ---------------------------------------------------------------------------
def suite6_positive_proportion() -> None:
    banner("Suite 6: Positive-Proportion Non-Vanishing Thresholds on Z_q-Towers")

    # 6A. Without BM(M): a single bad top orbit at layer k = n has worst-case
    # Fitting valuation bound (d0 * log q / (2 log l)) * n * phi(q^n) (per B08 eq. 1.4).
    # Verify that this exceeds c0 * d0 * q^n for all n > n_crit = 2*c0*q*log(l)/((q-1)*log(q)).
    print("  6A. Without BM(M): critical layer n_crit above which 1 bad top orbit breaks c0*d_n:")
    for q, l in [(3, 5), (3, 11), (5, 7), (7, 11)]:
        for label, c0 in [("Unmod Big (1/3)", 1 / 3), ("Decoupled (1.0)", 1.0), ("ChCore (1/10)", 0.1)]:
            n_crit = 2.0 * c0 * q * math.log(l) / ((q - 1) * math.log(q))
            n_test = int(math.floor(n_crit)) + 1
            ratio = (math.log(q) / (2.0 * math.log(l))) * n_test * ((q - 1) / q)
            assert ratio > c0
        print(f"    q={q}, l={l:2d}: n_crit(c0=1/3)={2*(1/3)*q*math.log(l)/((q-1)*math.log(q)):.2f}, "
              f"n_crit(c0=1)={2*1.0*q*math.log(l)/((q-1)*math.log(q)):.2f}, "
              f"n_crit(c0=1/10)={2*0.1*q*math.log(l)/((q-1)*math.log(q)):.2f}")

    # 6B. With BM(1) (eigenspace cyclicity) + single orbit g_inf = 1 on K0 = Q(sqrt(5)) (d0 = 2):
    # Top layer k = n non-vanishing leaves bad fraction beta_n <= q^{n-1} / q^n = 1/q.
    print("\n  6B. With BM(1) + single orbit g_inf=1 on d0=2 (Q(sqrt(5))), single top layer clean:")
    d0 = 2
    for name, num_chars, q_min in [
        ("HostEx n=2 decoupled (2 chars, sum < d0)", 2, 3),
        ("HostEx n=3 decoupled (4 chars, sum < d0)", 4, 3),
        ("HostEx n=3 unmod Big (b1=2 chars < d0/3)", 2, 5),
        ("ChCore decoupled (10 roots, sum < d0)", 10, 7),
        ("ChCore unified (max < d0/10)", 1, 7),
    ]:
        # Check exact beta = 1/q <= threshold
        for q in (3, 5, 7, 11):
            beta = Fraction(1, q)
            if "unmod Big" in name:
                ok = num_chars * beta < Fraction(d0, 3)
            elif "unified" in name:
                ok = beta < Fraction(d0, 10)
            else:
                ok = num_chars * beta < Fraction(d0, 1)
            if ok:
                print(f"    {name:42s}: SUFFICIENT at single top layer for q >= {q} (beta <= 1/{q})")
                break

    print("  [PASS] Suite 6 passed.")


def main() -> int:
    suite1_lean_thresholds()
    gs_results = suite2_gs_towers()
    suite3_louboutin_zimmert_case2a(gs_results)
    suite4_case2b_obstruction()
    suite5_exact_omega_L_values()
    suite6_positive_proportion()
    banner("ALL 6 SUITES PASSED (EXIT 0)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
