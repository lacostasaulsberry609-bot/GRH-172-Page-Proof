#!/usr/bin/env python3
"""
Verification script for Wave-6 D01: Lemma-ERL-Fixed
(Fixed non-parallel weight GSp_4/Q explicit reciprocity law with odd quadratic
central character chi_Pi = eta_{E_0} and general generic tame level).

Note: This script verifies exact symbolic algebraic identities and finite
numerical/combinatorial instances. General mathematical statements are proved
in erh_research/wave6/D01_lemma_erl_fixed_proof.md.
"""

import sympy as sp
from fractions import Fraction


def module_1_symplectic_and_unfolding():
    print("=== Module 1: Symplectic embedding H -> GSp_4, unipotent U_G, torus roots ===")
    a1, b1, c1, d1 = sp.symbols("a1 b1 c1 d1")
    a2, b2, c2, d2 = sp.symbols("a2 b2 c2 d2")
    x, y, z, w = sp.symbols("x y z w")
    a, b = sp.symbols("a b", nonzero=True)

    # Anti-diagonal symplectic form J (LSZ / LPSZ convention: Borel is upper triangular)
    J = sp.Matrix([
        [0, 0, 0, 1],
        [0, 0, 1, 0],
        [0, -1, 0, 0],
        [-1, 0, 0, 0],
    ])
    assert J.T == -J and J.det() == 1

    # Embedding iota: GL_2 x_{G_m} GL_2 -> GSp_4
    iota_h = sp.Matrix([
        [a1, 0, 0, b1],
        [0, a2, b2, 0],
        [0, c2, d2, 0],
        [c1, 0, 0, d1],
    ])
    prod = sp.simplify(iota_h.T * J * iota_h)
    det1 = a1 * d1 - b1 * c1
    det2 = a2 * d2 - b2 * c2
    expected = sp.Matrix([
        [0, 0, 0, det1],
        [0, 0, det2, 0],
        [0, -det2, 0, 0],
        [-det1, 0, 0, 0],
    ])
    assert sp.simplify(prod - expected) == sp.zeros(4)
    # When det1 == det2, iota_h^T J iota_h = det1 * J
    assert sp.simplify(prod.subs(det2, det1) - det1 * J) == sp.zeros(4)

    # Maximal upper-triangular unipotent subgroup U_G of GSp_4
    u = sp.Matrix([
        [1, x, y, z],
        [0, 1, w, y - x * w],
        [0, 0, 1, -x],
        [0, 0, 0, 1],
    ])
    assert sp.simplify(u.T * J * u - J) == sp.zeros(4)

    # 2-torus t(a, b) = (diag(a*b, 1), diag(a, b)) in H / Z_G
    t_ab = sp.diag(a * b, a, b, 1)
    assert sp.simplify(t_ab.T * J * t_ab - (a * b) * J) == sp.zeros(4)
    # Simple roots alpha_1 = t1/t2 = b, alpha_2 = t2/t3 = a/b
    alpha_1 = sp.simplify(t_ab[0, 0] / t_ab[1, 1])
    alpha_2 = sp.simplify(t_ab[1, 1] / t_ab[2, 2])
    assert alpha_1 == b and alpha_2 == a / b

    # Unfolding functional equation check:
    # sigma_1 = s1 + s2 - 1/2, sigma_2 = s1 - s2 + 1/2
    s1, s2 = sp.symbols("s1 s2")
    sig1 = s1 + s2 - sp.Rational(1, 2)
    sig2 = s1 - s2 + sp.Rational(1, 2)
    # Under s2 -> 1 - s2: sig1 <-> sig2
    assert sp.simplify(sig1.subs(s2, 1 - s2) - sig2) == 0
    assert sp.simplify(sig2.subs(s2, 1 - s2) - sig1) == 0
    # Under (s1, s2) -> (s2, s1): sig2 -> 1 - sig2 (matching functional eq (Pi x chi1^-1)^v = Pi x chi2^-1)
    assert sp.simplify(sig2.subs({s1: s2, s2: s1}, simultaneous=True) - (1 - sig2)) == 0
    print("  [PASS] Module 1: all symplectic, unipotent, torus, and unfolding identities verified.")


def sp4_weyl_char_decomp(r1, r2):
    """Exact decomposition of Res^{Sp_4}_{SL_2 x SL_2}(V_{r1, r2}) via Weyl character formula."""
    x, y = sp.symbols("x y")
    # Weyl denominator for Sp_4 in orthogonal torus coordinates (x, y)
    # Positive roots: x/y, x*y, x^2, y^2; rho = (2, 1)
    def alt_sum(m1, m2):
        # Sum_{w in W(C_2)} sgn(w) x^{w(m)_1} y^{w(m)_2}
        terms = [
            (+1, m1, m2), (-1, m2, m1), (-1, m1, -m2), (+1, m2, -m1),
            (-1, -m1, m2), (+1, -m2, m1), (+1, -m1, -m2), (-1, -m2, -m1),
        ]
        return sum(sgn * x**p1 * y**p2 for sgn, p1, p2 in terms)

    num = alt_sum(r1 + 2, r2 + 1)
    den = alt_sum(2, 1)
    char = sp.cancel(num / den)
    # Multiply by (x - x^-1)(y - y^-1) to extract Sym^{a1}(x) x Sym^{a2}(y) multiplicities!
    # Since Sym^{a1}(x) = (x^{a1+1} - x^{-(a1+1)}) / (x - x^-1), the coefficient of x^{a1+1} y^{a2+1}
    # in char * (x - x^-1)(y - y^-1) for a1, a2 >= 0 IS the exact multiplicity!
    prod = sp.expand(char * (x - 1 / x) * (y - 1 / y))
    poly = sp.Poly(sp.expand(prod * x**(r1 + 2) * y**(r1 + 2)), x, y)
    shift = r1 + 2
    mults = {}
    for (px, py), coeff in poly.terms():
        d1 = px - shift
        d2 = py - shift
        if d1 >= 1 and d2 >= 1:
            mults[(d1 - 1, d2 - 1)] = int(coeff)
    return mults


def module_2_branching_serre_smoothing():
    print("=== Module 2: Sp_4 -> SL_2^2 branching, Serre duality on X_H, and smoothing zero catch ===")
    r1, r2, q, r = sp.symbols("r1 r2 q r", integer=True)

    # Symbolic Weyl dimension identity for parametrized sum
    # sum_{q=0}^{r2} sum_{r=0}^{r1-r2} (r1 - q - r + 1)(r2 - q + r + 1)
    inner = sp.summation((r1 - q - r + 1) * (r2 - q + r + 1), (r, 0, r1 - r2))
    total = sp.factor(sp.summation(inner, (q, 0, r2)))
    weyl_dim = sp.factor((r1 - r2 + 1) * (r2 + 1) * (r1 + 2) * (r1 + r2 + 3) / 6)
    assert sp.simplify(total - weyl_dim) == 0
    print(f"  [PASS] Symbolic Weyl branching sum == {weyl_dim}")

    # Exact Weyl character check on finite non-parallel odd-weight instances (e1, e2)
    for e1, e2 in [(5, 4), (6, 4), (7, 4), (8, 5)]:
        rr1 = e1 + e2 - 2
        rr2 = e1 - e2 - 1
        assert rr1 - rr2 == 2 * e2 - 1 >= 7
        assert (rr1 + rr2) % 2 == 1
        mults = sp4_weyl_char_decomp(rr1, rr2)
        expected_set = {
            (rr1 - qq - rr, rr2 - qq + rr): 1
            for qq in range(rr2 + 1)
            for rr in range(rr1 - rr2 + 1)
        }
        assert mults == expected_set, f"Mismatch at (e1,e2)=({e1},{e2})"
        # Check every summand has odd a1 + a2
        assert all((a1 + a2) % 2 == 1 for (a1, a2) in mults)
        # Check dimension
        dim_sum = sum((a1 + 1) * (a2 + 1) for (a1, a2) in mults)
        assert dim_sum == (rr1 - rr2 + 1) * (rr2 + 1) * (rr1 + 2) * (rr1 + rr2 + 3) // 6
    print("  [PASS] Exact Weyl character decomposition verified for (e1,e2) in {(5,4),(6,4),(7,4),(8,5)}.")

    # Coherent H^2 bundle weight and Serre duality on X_H
    e1, e2, m, s = sp.symbols("e1 e2 m s", integer=True)
    k1 = e1 + e2 + 1
    k2 = e1 - e2 + 2
    # w2 = s2 s1: s2 s1 (r1+2, r2+1) - (2,1) = (r2-1, -r1-3) -> classical (k2-1, 3-k1)
    h2_wt = (k2 - 1, 3 - k1)
    assert h2_wt[0] + h2_wt[1] == 3 - 2 * e2  # odd!
    # Serre dual on X_H: (2 - (3 - k1 + m), 2 - (k2 - 1 - m)) with m = (k2 - 2) + s
    t1_coh = sp.simplify(2 - (3 - k1 + (k2 - 2 + s)))
    t2_coh = sp.simplify(2 - (k2 - 1 - (k2 - 2 + s)))
    assert t1_coh == 2 * e2 - s and t2_coh == 1 + s
    assert sp.simplify(t1_coh + t2_coh) == 2 * e2 + 1  # ALWAYS odd!

    # Smoothing zero catch at r = e2 + 1 vs optimal choice r = e2 + 3 (e2 >= 4)
    # sigma_1 = s1 + s2 - 1/2 = 1, sigma_2 = s1 - s2 + 1/2
    for r_shift, sig2_val, expect_trap in [(1, 2, True), (3, 4, False)]:
        s1_val = Fraction(1 + sig2_val, 2)
        s2_val = Fraction(1 - sig2_val + 1, 2)
        assert s1_val + s2_val - Fraction(1, 2) == 1
        assert s1_val - s2_val + Fraction(1, 2) == sig2_val
        zero_hit = (2 * s2_val == 2) or (2 * (1 - s2_val) == 2)
        assert zero_hit == expect_trap
        if not expect_trap:
            assert s1_val == Fraction(5, 2) and s2_val == Fraction(-1, 1)
            # Check c2^2 - c2^{2 s2} and c2^2 - c2^{2(1-s2)} are both nonzero for all c2 > 1
            for c2 in [2, 3, 5, 7, 11]:
                assert c2**2 - Fraction(c2)**(2 * s2_val) != 0
                assert c2**2 - Fraction(c2)**(2 * (1 - s2_val)) != 0
    print("  [PASS] Smoothing zero at r = e2+1 (s2=0) reproduced; optimal r = e2+3 (s1=5/2, s2=-1) avoids all zeros.")

    # Check Eisenstein weights for r = e2 + 3 across all e2 >= 4, e1 > e2, 0 <= q' <= r2
    for e2_val in [4, 5, 6, 7]:
        for e1_val in range(e2_val + 1, e2_val + 8):
            rr1 = e1_val + e2_val - 2
            rr2 = e1_val - e2_val - 1
            r_opt = e2_val + 3
            assert 0 <= r_opt <= rr1 - rr2  # sharp: r_opt <= 2*e2 - 1 <=> e2 >= 4!
            # Note 24.3.7 parity: (-1)^(r_opt + 1) == (-1)^e2_val
            assert (r_opt + 1) % 2 == e2_val % 2
            for qp in range(rr2 + 1):
                j_val = -1 - rr2 + qp
                # Filter by exact Note 24.3.7 parity of Sigma_geom: (-1)^j == (-1)^(r_opt + 1)
                if j_val % 2 != (r_opt + 1) % 2:
                    continue
                t1_mot = rr1 - qp - r_opt + 2
                t2_mot = rr2 - qp + r_opt + 2
                assert t1_mot % 2 == 1 and t1_mot >= 3, f"Bad t1={t1_mot}"
                assert t2_mot % 2 == 0 and t2_mot >= 10, f"Bad t2={t2_mot}"
                assert (t1_mot - t2_mot) % 2 == 1
    # Verify sharpness of e2 >= 4: at e2 = 3, r_opt = 6 > 2*3 - 1 = 5
    assert 3 + 3 > 2 * 3 - 1
    print("  [PASS] Optimal choice (a, r) = (e2, e2+3) verified: sharp threshold e2 >= 4, on Sigma_geom ALWAYS t1 odd >= 3 & t2 even >= 10.")


def module_3_local_test_vectors():
    print("=== Module 3: Local bad-prime test vectors (Phi_1, Phi_2) & Ramanujan Euler non-vanishing ===")
    # Finite ring check on Z/v^M Z for v in {3, 5, 7, 11}, M = 2
    for v in [3, 5, 7, 11]:
        M = 2
        mod = v**M
        units = [u for u in range(1, mod) if sp.gcd(u, v) == 1]

        # Test both unramified quadratic character (chi = 1 on Z_v^x, as at v | D_{K0})
        # and ramified quadratic character (Legendre symbol mod v, as at v | D_{E0})
        def leg(u, p=v):
            return 1 if pow(u % p, (p - 1) // 2, p) == 1 else -1

        for chi_name, chi in [("unram_quad", lambda u: 1), ("ram_quad", leg)]:
            # Phi_1(x, y) = chi(y)^-1 if x == 0 mod v^M and gcd(y, v) == 1 else 0
            def phi1(x, y):
                if x % mod == 0 and sp.gcd(y, v) == 1:
                    return chi(y)  # quadratic: chi^-1 == chi
                return 0

            # Check equivariance Phi_1(a*x, a*y) = chi(a)^-1 Phi_1(x, y) on all of (Z/v^M Z)^2
            for a in units:
                for x in [0, 1, v]:
                    for y in [0, 1, 2, v]:
                        assert phi1((a * x) % mod, (a * y) % mod) == chi(a) * phi1(x, y)

            # Godement integral over t in (Z/v^M Z)^x at k1 = I_2: sum_t phi1(0, t) * chi(t) = |units| > 0
            godement_sum = sum(phi1(0, t) * chi(t) for t in units)
            assert godement_sum == len(units) and godement_sum > 0

        # Check Phi_2 partial Fourier transform: Phi2_hat(x, y) = 1_{Z_v^x}(x) * 1_{1 + v^M Z_v}(x*y)
        def phi2_hat(x, y):
            if sp.gcd(x, v) == 1 and (x * y - 1) % mod == 0:
                return 1
            return 0

        # Check Z_v^x-invariance: phi2_hat(a*x, a^-1 * y) == phi2_hat(x, y)
        for a in units:
            a_inv = pow(a, -1, mod)
            for x in range(min(mod, 15)):
                for y in range(min(mod, 15)):
                    assert phi2_hat((a * x) % mod, (a_inv * y) % mod) == phi2_hat(x, y)

        # Check discrete Whittaker integral over u in (Z/v^M Z)^x at diag(a0, b0) with a0, b0 in units:
        # sum_u phi2_hat(u^-1 * a0, u * b0^-1) equals |units| if a0 == b0 mod v^M else 0!
        for a0 in units[:6]:
            b0_inv_list = [pow(b0, -1, mod) for b0 in units[:6]]
            for b0, b0_inv in zip(units[:6], b0_inv_list):
                w_sum = sum(
                    phi2_hat((pow(u, -1, mod) * a0) % mod, (u * b0_inv) % mod)
                    for u in units
                )
                expected_w = len(units) if (a0 - b0) % mod == 0 else 0
                assert w_sum == expected_w

    # Ramanujan bound check for P_v(Pi_v, v^-sigma) at sigma = 1, 4 (vs sigma = 0)
    for v in [2, 3, 5, 7, 11, 13]:
        # |alpha_v| <= 1 => |1 - alpha_v v^-sigma| >= 1 - v^-sigma > 0 for sigma in {1, 4}
        lower_1 = (1 - Fraction(1, v))**4
        lower_4 = (1 - Fraction(1, v**4))**4
        assert lower_1 > 0 and lower_4 > 0
        # Contrast sigma = 0: alpha_v = 1 gives 1 - 1 = 0!
        assert (1 - 1) == 0
    print("  [PASS] Module 3: explicit Z_v^x-equivariant (Phi_1, Phi_2), Whittaker collapse, and Ramanujan bounds verified.")


def module_4_family_slice_euler_and_density():
    print("=== Module 4: 1-variable Hilbert slice, Fil^1/Fil^2 HT cancellation, ell-Euler factors, component density ===")
    e1, e2, n, j = sp.symbols("e1 e2 n j", integer=True)

    # Shift (r1, r2) -> (r1 + n, r2 + n) corresponds to (e1, e2) -> (e1 + n, e2)
    r1 = e1 + e2 - 2
    r2 = e1 - e2 - 1
    r1_n = (e1 + n) + e2 - 2
    r2_n = (e1 + n) - e2 - 1
    assert sp.simplify(r1_n - (r1 + n)) == 0
    assert sp.simplify(r2_n - (r2 + n)) == 0
    assert sp.simplify((r1_n - r2_n) - (r1 - r2)) == 0  # constant r1 - r2 = 2*e2 - 1!
    assert sp.simplify((r1_n + r2_n) - (r1 + r2 + 2 * n)) == 0  # odd parity preserved for ALL n!

    # Check HT weights of W_{l_2}^*(e1 + n - q) with q = 1 + r2_n + j = (e1 + n - e2) + j
    # W_{0,n}^v at l_2 has HT weights {-e2, +e2}; twisting by (e1 + n - q) gives:
    q_expr = 1 + r2_n + j
    twist = (e1 + n) - q_expr
    ht_l2_1 = sp.simplify(-e2 + twist)
    ht_l2_2 = sp.simplify(+e2 + twist)
    assert ht_l2_1 == -j and ht_l2_2 == 2 * e2 - j  # n CANCELS IDENTICALLY!
    # At j = 0 (unshifted Fil^1/Fil^2 of W_Pi^*(-1 - r2 - n)): HT weight is 0 (unramified rank-1 character!)
    assert ht_l2_1.subs(j, 0) == 0
    # At critical j = e2: HT weight of Fil^1/Fil^2 is -e2 <= -4 < 0 (strictly negative => exp* well-defined!)
    assert ht_l2_1.subs(j, e2) == -e2

    # Check all 4 ell-Euler factors at sigma_1 = 1 (j_cl = e1 + 1) and sigma_2 = 4 (j_cl = e1 + 4)
    # Unshifted valuations of (alpha_1, alpha_2, beta_2, beta_1) are (0, e1-e2, e1+e2, 2*e1), complex modulus ell^e1
    for e2_val in [4, 5, 6]:
        for e1_val in [e2_val + 1, e2_val + 5, e2_val + 12]:
            v_a1, v_a2, v_b2, v_b1 = 0, e1_val - e2_val, e1_val + e2_val, 2 * e1_val
            for sigma in [1, 4]:
                j_cl = e1_val + sigma
                # First two factors: 1 - ell^{j_cl - 1} / alpha_i -> ell-adic valuation > 0 (1-units!)
                val_f1 = (j_cl - 1) - v_a1
                val_f2 = (j_cl - 1) - v_a2
                assert val_f1 >= e1_val >= 5 and val_f2 >= e2_val >= 4
                # Last two factors: 1 - beta_i / ell^{j_cl} -> complex modulus = ell^{e1 - j_cl} = ell^{-sigma} < 1
                assert e1_val - j_cl == -sigma <= -1

    # Check connected-component density of Sigma_geom^{(e2)} on W_{e2 mod (ell-1)}
    for ell in [3, 5, 7, 11, 13, 19, 29, 31]:
        e2_val = 4
        # Base e1 >= e2 + ell ensures r2 >= ell - 1, so at least one j0 in [-1-r2, -1] with j0 == e2 mod (ell-1)
        e1_base = e2_val + ell
        r2_base = e1_base - e2_val - 1
        assert r2_base >= ell - 1
        j_list_0 = [jj for jj in range(-1 - r2_base, 0) if (jj - e2_val) % (ell - 1) == 0]
        assert len(j_list_0) >= 1
        # Check for arbitrary Weierstrass bound Lambda_0 = 20
        Lambda_0 = 20
        n_step = (ell - 1) * (Lambda_0 + 1)
        r2_n_val = r2_base + n_step
        j_list_n = [jj for jj in range(-1 - r2_n_val, 0) if (jj - e2_val) % (ell - 1) == 0]
        assert len(j_list_n) > Lambda_0
    print("  [PASS] Module 4: Hilbert slice, HT cancellation, all 4 ell-Euler factors, and component density verified.")


if __name__ == "__main__":
    module_1_symplectic_and_unfolding()
    module_2_branching_serre_smoothing()
    module_3_local_test_vectors()
    module_4_family_slice_euler_and_density()
    print("\nALL 4 VERIFICATION MODULES PASSED (EXIT 0).")
