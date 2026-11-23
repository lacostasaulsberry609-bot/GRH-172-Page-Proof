#!/usr/bin/env python3
"""
Verification script for Wave-7 E02 (D05-L2):
Two-variable rigid analytic Spin p-adic L-function on the parallel-shift
Coleman curve U x W_a via Boxer-Pilloni H^2 families and double Eisenstein pairing.

NOTE: This script verifies exact symbolic identities and finite parameter instances.
General theorems are established by the proofs in:
  erh_research/wave7/E02_prove_d05_l2_bp_spin_padic_l.md
"""

import sys
import sympy as sp


def module1_bruhat_and_iwahori_containment():
    print("=== [Module 1] w1-Bruhat transversality, tube pullback, and Iwahori containment ===")
    J = sp.Matrix([
        [0, 0, 0, 1],
        [0, 0, 1, 0],
        [0, -1, 0, 0],
        [-1, 0, 0, 0],
    ])
    Ups = sp.Matrix([
        [1, 0, 0, 0],
        [1, 1, 0, 0],
        [0, 0, 1, 0],
        [0, 0, -1, 1],
    ])
    w1 = sp.Matrix([
        [1, 0, 0, 0],
        [0, 0, 1, 0],
        [0, -1, 0, 0],
        [0, 0, 0, 1],
    ])
    g = w1 * Ups
    assert Ups.T * J * Ups == J, "Ups not symplectic"
    assert w1.T * J * w1 == J, "w1 not symplectic"
    assert g.T * J * g == J, "g = w1*Ups not symplectic"

    # Generic point of FL_H = P^1 x P^1: L_H([a1:c1], [a2:c2])
    a1, c1, a2, c2 = sp.symbols("a1 c1 a2 c2")
    L_H = sp.Matrix([
        [a1, 0],
        [0, a2],
        [0, c2],
        [c1, 0],
    ])
    M = g * L_H
    # Closure of C_{w1} = {L : e1 in L} <=> rows (1,2,3) [0-indexed] have rank <= 1
    sub = M[1:, :]
    minors = [sp.factor(sub.extract([i, j], [0, 1]).det()) for i in range(3) for j in range(i + 1, 3)]
    expected_minors = {sp.factor(a1 * c2), sp.factor(-c1 * c2), sp.factor(a1 * c2 + a2 * c1)}
    assert set(minors) == expected_minors, f"Unexpected minors: {minors}"
    # Verify only solution on P^1 x P^1 is c1 = c2 = 0 (i.e. (inf, inf)):
    # If c2 != 0: a1*c2 = 0 => a1 = 0, -c1*c2 = 0 => c1 = 0 (impossible in P^1).
    # Thus c2 = 0 => a2 != 0 => a2*c1 = 0 => c1 = 0.
    # Also check disjointness from C_{w0} = {<e1, e2>} <=> rows (2,3) vanish identically:
    rows23 = M[2:, :]
    # rows23 = [[-a1, -a2], [c1, -c2]]; zero iff a1=c1=a2=c2=0 (impossible on P^1 x P^1).
    assert rows23 == sp.Matrix([[-a1, -a2], [c1, -c2]])

    # Local Schubert coordinates (z1, z2, z3) near w1 = <e1, e3>:
    # L(z1, z2, z3) = col-span of [[1, 0], [z1, z3], [0, 1], [z2, z1]]
    M_loc = M.subs({a1: 1, a2: 1})
    R = M_loc.extract([0, 2], [0, 1])
    assert sp.simplify(R.det()) == -1
    M_std = sp.simplify(M_loc * R.inv())
    z1, z2, z3 = M_std[1, 0], M_std[3, 0], M_std[1, 1]
    assert M_std[3, 1] == -z1, f"Isotropy check failed: {M_std[3,1]} vs {-z1}"
    assert sp.simplify(M_std.T * J * M_std) == sp.zeros(2, 2), "Lagrangian check failed"
    assert (z1, z2, z3) == (-c2, c1 + c2, -c2), f"Unexpected coords {(z1, z2, z3)}"
    Jac = sp.Matrix([[sp.diff(z1, c1), sp.diff(z1, c2)], [sp.diff(z2, c1), sp.diff(z2, c2)]])
    assert Jac.det() == 1, f"Jacobian det = {Jac.det()} != 1"

    # Action of t_Kl = diag(1, l, l, l^2) and t_Si = diag(1, 1, l, l) on (z1, z2, z3):
    l, Z1, Z2, Z3 = sp.symbols("l Z1 Z2 Z3")
    L_chart = sp.Matrix([[1, 0], [Z1, Z3], [0, 1], [Z2, -Z1]])
    assert sp.simplify(L_chart.T * J * L_chart) == sp.zeros(2, 2), "L_chart not Lagrangian"
    def act_chart(tmat):
        A = tmat * L_chart
        A_std = sp.simplify(A * A.extract([0, 2], [0, 1]).inv())
        return (A_std[1, 0], A_std[3, 0], A_std[1, 1])

    t_Kl = sp.diag(1, l, l, l**2)
    t_Si = sp.diag(1, 1, l, l)
    assert act_chart(t_Kl) == (l * Z1, l**2 * Z2, Z3)
    assert act_chart(t_Si) == (Z1, l * Z2, Z3 / l)
    assert act_chart(t_Kl * t_Si) == (l * Z1, l**3 * Z2, Z3 / l)

    # Check Iwahori containment: g_beta = t_Kl^beta * t_Si * w1 * Ups
    # For h1 = [[t1, l^(2*beta+1)*u1p], [l^(2*beta+1)*v1p, t4]] in K1(l^(2*beta+1))
    # and h2 = [[b11, b12], [l*c21, b22]] in Iw_2(l) with det(h1) = det(h2):
    t1, u1p, v1p, b11, b12, c21, b22 = sp.symbols("t1 u1p v1p b11 b12 c21 b22")
    d = b11 * b22 - l * b12 * c21
    for beta in [1, 2, 3, 4]:
        # Set t4 = (d + l^(4*beta+2)*u1p*v1p) / t1 so det(h1) = d exactly
        t4 = (d + l**(4 * beta + 2) * u1p * v1p) / t1
        h1 = sp.Matrix([[t1, l**(2 * beta + 1) * u1p], [l**(2 * beta + 1) * v1p, t4]])
        h2 = sp.Matrix([[b11, b12], [l * c21, b22]])
        H_emb = sp.Matrix([
            [h1[0, 0], 0, 0, h1[0, 1]],
            [0, h2[0, 0], h2[0, 1], 0],
            [0, h2[1, 0], h2[1, 1], 0],
            [h1[1, 0], 0, 0, h1[1, 1]],
        ])
        g_beta = sp.diag(1, l**beta, l**(beta + 1), l**(2 * beta + 1)) * w1 * Ups
        conj = sp.simplify(g_beta * H_emb * g_beta.inv())
        # Verify every entry is a polynomial in l (integral at l, no negative powers of l),
        # and every strictly lower-triangular entry (i > j) is divisible by l!
        for i in range(4):
            for j in range(4):
                expr = sp.together(conj[i, j])
                num, den = sp.fraction(expr)
                assert not den.has(l), f"Denominator has l at beta={beta}, ({i},{j}): {expr}"
                if i > j:
                    val_at_0 = sp.simplify(num.subs(l, 0))
                    assert val_at_0 == 0, f"Lower entry ({i},{j}) not div by l at beta={beta}: {num}"
    print("  PASS: g = w1*Ups transverse with Jac=+1, disjoint from C_{w0}, and g_beta-conjugation lands in Iw(l) for beta=1..4.")


def module2_locally_analytic_branching_and_weights():
    print("=== [Module 2] Locally analytic M_{w1}-branching, algebraic degree bounds, and Amice-Velu count ===")
    t1, t2, z, y, l, beta_sym = sp.symbols("t1 t2 z y l beta")
    # Action of g_beta * T_H * g_beta^-1 on L_{w1} = <e1, e3>:
    # On L_{w1}, t_Kl^beta * t_Si acts as diag(1, l^(beta+1)).
    # Earlier g*T_H*g^-1 on <e1,e3> was [[t1, 0], [t2 - t1, t2]].
    # Conjugating by diag(1, l^B) (B = beta + 1) gives [[t1, 0], [l^B*(t2 - t1), t2]].
    B = sp.Symbol("B")
    m_B = sp.Matrix([[t1, 0], [B * (t2 - t1), t2]])
    # Fractional linear action on z: z' = (r + s*z) / (p + q*z) = (B*(t2 - t1) + t2*z) / t1
    z_prime = sp.simplify((m_B[1, 0] + m_B[1, 1] * z) / (m_B[0, 0] + m_B[0, 1] * z))
    # Change variable y = 1 + z / B  <=>  z = B * (y - 1):
    y_prime = sp.simplify(1 + z_prime.subs(z, B * (y - 1)) / B)
    assert y_prime == (t2 / t1) * y, f"Unexpected y' = {y_prime}"

    # Verify weight transformation of F_s(y) = y^s:
    # (m_B . F_s)(y) = t1^a * t2^b * (t2/t1)^s * y^s = t1^(a - s) * t2^(b + s) * y^s
    # For kappa_2(n) = (a, b) = (r2 + n + 2, -r1 - n):
    # Serre dual on X_H (Omega^2 = omega_1^2 x omega_2^2):
    # w1 = 2 - (a - s) = s - r2 - n,  w2 = 2 - (b + s) = r1 + n + 2 - s
    r1, r2, n, s, e2, r, j1 = sp.symbols("r1 r2 n s e2 r j1")
    a_wt = r2 + n + 2
    b_wt = -r1 - n
    w1_dual = 2 - (a_wt - s)
    w2_dual = 2 - (b_wt + s)
    assert sp.simplify(w1_dual + w2_dual - (r1 - r2 + 2)) == 0

    # Set s = r2 + n + (2*e2 - r + j1) with r1 - r2 = 2*e2 - 1:
    s_expr = r2 + n + (2 * e2 - r + j1)
    w1_expr = sp.simplify(w1_dual.subs(s, s_expr))
    w2_expr = sp.simplify(w2_dual.subs({s: s_expr, r1: r2 + 2 * e2 - 1}))
    assert w1_expr == 2 * e2 - r + j1
    assert w2_expr == r + 1 - j1
    assert sp.simplify(w1_expr + w2_expr) == 2 * e2 + 1

    # Check Novodvorsky Eisenstein parameters:
    # E1 = E_{[j1, b1]} with b1 = 2*e2 - 1 - r => weight = j1 + b1 + 1 = 2*e2 - r + j1 = w1_expr
    # E1 = theta^{j1} (E_{[0, b1 - j1]}) where holomorphic weight is t1 = b1 - j1 + 1 = 2*e2 - r - j1
    # E2 = E_{[0, r - j1]} => holomorphic weight = r + 1 - j1 = w2_expr
    b1 = 2 * e2 - 1 - r
    t1_hol = b1 - j1 + 1
    assert sp.simplify(t1_hol - (2 * e2 - r - j1)) == 0
    # Check spectral parameters s1 = (1 + j1 - b1)/2, s2 = (1 + 0 - (r - j1))/2:
    s1_spec = (1 + j1 - b1) / 2
    s2_spec = (1 - (r - j1)) / 2
    sigma1 = sp.simplify(s1_spec + s2_spec - sp.Rational(1, 2))
    sigma2 = sp.simplify(s1_spec - s2_spec + sp.Rational(1, 2))
    assert sigma1 == 1 - e2 + j1
    assert sigma2 == 1 - e2 + r

    # Verify finite grid for BOTH targets:
    # Target 1 (primary): (j1_crit, r) = (e2, e2 + 3) => (sigma1, sigma2) = (1, 4), (s1, s2) = (5/2, -1)
    # Target 2 (dual):    (j1_crit, r) = (e2 - 1, e2 + 2) => (sigma1, sigma2) = (0, 3), (s1, s2) = (3/2, -1)
    checked = 0
    for ell in [3, 5, 7, 11, 13, 19]:
        for e2_val in [4, 5, 6, 7, 8, 10]:
            r2_0 = ell
            r1_0 = 2 * e2_val + ell - 1
            for n_val in [0, 2, 4, ell - 1, 2 * (ell - 1)]:
                r1_n = r1_0 + n_val
                r2_n = r2_0 + n_val
                deg_max = r1_n + r2_n + 2
                for mode, j1_crit, r_val in [
                    ("primary", e2_val, e2_val + 3),
                    ("dual", e2_val - 1, e2_val + 2),
                ]:
                    assert 0 <= r_val <= r1_n - r2_n
                    assert (j1_crit + r_val) % 2 == 1, "Note 24.3.7 parity mismatch"
                    # Check algebraic polynomial degree 0 <= s(n, j1) <= deg_max
                    # across ALL non-critical j1 in [-r2_n - 1, -1] and ALL critical j1 in [0, r_val]:
                    for j1_val in range(-r2_n - 1, r_val + 1):
                        s_val = r2_n + (2 * e2_val - r_val + j1_val)
                        assert 0 <= s_val < deg_max, f"s={s_val} out of [0, {deg_max})"
                        if (j1_val - j1_crit) % 2 == 0:
                            w1_v = 2 * e2_val - r_val + j1_val
                            w2_v = r_val + 1 - j1_val
                            t1_v = 2 * e2_val - r_val - j1_val
                            assert w1_v % 2 == 1, "w1 must be odd"
                            assert w2_v % 2 == 0, "w2 must be even"
                            if j1_val <= -1:
                                assert t1_v >= 3 and t1_v % 2 == 1
                                assert w2_v >= (10 if mode == "primary" else 8)
                            if j1_val == j1_crit:
                                assert w2_v == 4
                    # Count critical integers j1 in [0, r_val - 2] with same parity as j1_crit:
                    crit_pts = [j for j in range(0, r_val - 1) if (j - j1_crit) % 2 == 0]
                    if mode == "primary":
                        assert len(crit_pts) >= 3, f"Need >=3 crit pts for H_2 uniqueness (e2>=4), got {crit_pts}"
                    elif e2_val >= 5:
                        assert len(crit_pts) >= 3, f"Need >=3 crit pts for dual mode (e2>=5), got {crit_pts}"
                    if e2_val >= 7:
                        assert len(crit_pts) >= 4, f"Need >=4 crit pts for e2>=7, got {crit_pts}"
                    checked += 1
    print(f"  PASS: Purely multiplicative y' = (t2/t1)*y verified; all bounds verified on {checked} (ell, e2, n, mode) instances.")


def module3_small_slope_and_hecke_iwahori_klingen():
    print("=== [Module 3] Boxer-Pilloni / LR H^2 strictly small slope & Iwahori-to-Klingen projection ===")
    # Check strictly small slope bounds along U:
    # h_Kl = 0 < r1(n) - r2(n) - 2 = 2*e2 - 3
    # h_Si = (ell + 1)/2 < r2(n) + 1 = ell + n + 1 < r1(n) + 2
    cnt = 0
    for ell in [3, 5, 7, 11, 13, 17, 19, 23, 29, 31]:
        h_Si = (ell + 1) // 2
        for e2_val in [4, 5, 6, 8, 12]:
            for n_val in [0, 1, 2, 4, 10, 50]:
                r2_n = ell + n_val
                r1_n = 2 * e2_val + ell - 1 + n_val
                assert 0 < r1_n - r2_n - 2, "H^2 strictly small slope Kl bound failed"
                assert h_Si < r2_n + 1, "Global small slope Si bound failed"
                assert h_Si < r1_n + 2, "H^2 small slope Si bound failed"
                # Check n >= 2 pairwise valuation gaps != 1:
                if n_val >= 2:
                    v_a = sp.Rational(ell + 1, 2)
                    v_b = v_a + n_val
                    v_c = r1_n + 2 + v_a
                    v_d = r1_n + 2 + v_b
                    vals = [v_a, v_b, v_c, v_d]
                    for i in range(4):
                        for j in range(i + 1, 4):
                            assert vals[j] - vals[i] >= 2, f"Gap < 2 at n={n_val}"
                cnt += 1

    # Symbolic 2x2 Casselman T_{s2} on W_{Kl-ord} = span(v_alpha, v_beta):
    l, q = sp.symbols("l q")
    Ts2 = sp.Matrix([
        [(l - 1) / (1 - q), (l - 1 / q) / (1 - 1 / q)],
        [(l - q) / (1 - q), (l - 1) / (1 - 1 / q)],
    ])
    assert sp.simplify((Ts2 - l * sp.eye(2)) * (Ts2 + sp.eye(2))) == sp.zeros(2, 2)
    v_Kl = sp.Matrix([1, 1])
    assert sp.simplify(Ts2 * v_Kl - l * v_Kl) == sp.zeros(2, 1)
    v_alpha = sp.Matrix([1, 0])
    tr_img = sp.simplify((Ts2 + sp.eye(2)) * v_alpha)
    c1_ratio = sp.simplify(tr_img[0] / (l + 1))
    assert sp.simplify(c1_ratio - (l - q) / ((l + 1) * (1 - q))) == 0
    assert sp.simplify(c1_ratio.subs(q, -1)) == sp.Rational(1, 2)
    # Check limit as q^-1 -> 0 (n -> inf):
    inv_q = sp.Symbol("inv_q")
    c1_inv = sp.cancel(c1_ratio.subs(q, 1 / inv_q))
    lim_val = sp.simplify(c1_inv.subs(inv_q, 0))
    assert lim_val == 1 / (l + 1), f"Unexpected lim_val={lim_val}"
    print(f"  PASS: Strictly small slope & gap>=2 verified on {cnt} instances; c1(-1)=1/2 and lim_{{q^-1->0}} c1 = 1/(l+1) certified.")


def module4_bad_primes_smoothing_and_dual_branch_euler():
    print("=== [Module 4] Bad-prime constant term vanishing, smoothing factors, and dual-branch Euler factors ===")
    # 1. Verify Phi_{2,v}(0, z) = 0 and \widehat{Phi}_{2,v}(0, 0) = 0 on Z/v^2 Z for v in {3,5,7,11}:
    for v in [3, 5, 7, 11]:
        N = v * v
        # \widehat{Phi}_{2,v}^{(2)}(x, y) = 1_{(Z/N)^x}(x) * 1_{1 + vZ/N}(x*y)
        def phi2_hat2(x, y):
            if x % v == 0:
                return 0
            return 1 if ((x * y - 1) % v == 0) else 0

        # Check Phi_{2,v}(0, z) = sum_y phi2_hat2(0, y) * zeta^{y*z} == 0:
        for z_val in range(N):
            assert all(phi2_hat2(0, y) == 0 for y in range(N))
        # Check \widehat{Phi}_{2,v}(0, 0) = sum_x phi2_hat2(x, 0) == 0:
        assert sum(phi2_hat2(x, 0) for x in range(N)) == 0

    # 2. Check smoothing factors at (s1, s2) = (5/2, -1) and (3/2, -1):
    for name, s1, s2 in [("primary (e2, e2+3)", sp.Rational(5, 2), -1), ("dual (e2-1, e2+2)", sp.Rational(3, 2), -1)]:
        for exp in [2 * s1, 2 * (1 - s1), 2 * s2, 2 * (1 - s2)]:
            assert exp != 2, f"Smoothing zero at {name}: exp={exp}"
        # Also verify w2 = 2*(1 - s2) = 4 != 0, 2:
        w2 = 2 * (1 - s2)
        assert w2 == 4
        for c2 in [2, 3, 5, 7, 11]:
            assert c2**2 - c2**w2 != 0
            assert 1 - sp.Rational(1, c2**w2) != 0

    # 3. Verify all 4 LPSZ l-Euler factors at sigma1 in {0, 1} and sigma2 in {3, 4} for BOTH V and V':
    # Remember: for Pi_0 and Pi_0' = Pi_0 x eta_{E0}, eta_{E0}(l) in {+1, -1} preserves {+sqrt(a_l), -sqrt(a_l)}
    # and {+sqrt(b_l), -sqrt(b_l)}.
    # At arithmetic point s_arith = e1 + sigma (so q = e1 - 1 + sigma):
    # The 4 LPSZ factors are:
    #   (1 - l^{q}/alpha), (1 - l^{q}/beta), (1 - gamma/l^{q+1}), (1 - delta/l^{q+1})
    # Wait: check exact l-adic valuations for sigma in {0, 1, 3, 4}:
    # v_l(alpha) = v_l(beta) = (e1 - e2)/2
    # v_l(gamma) = v_l(delta) = (3*e1 + e2)/2
    euler_checked = 0
    for ell in [3, 5, 7, 11, 13, 19, 29]:
        for e2_val in [4, 5, 6, 8, 10]:
            e1_val = e2_val + ell + 1
            v_ab = sp.Rational(e1_val - e2_val, 2)
            v_cd = sp.Rational(3 * e1_val + e2_val, 2)
            for sigma in [0, 1, 3, 4]:
                # q_eff = e1 - 1 + sigma (so sigma=0 -> q=e1-1, sigma=1 -> q=e1, sigma=3 -> q=e1+2, sigma=4 -> q=e1+3)
                q_eff = e1_val - 1 + sigma
                # Check v_l(l^{q_eff} / alpha) and v_l(gamma / l^{q_eff + 1}):
                val_12 = q_eff - v_ab
                val_34 = v_cd - (q_eff + 1)
                # For sigma in {0, 1, 3, 4} with e2 >= 4:
                # val_12 = (e1 + e2)/2 - 1 + sigma > 0 ALWAYS
                # val_34 = (e1 + e2)/2 - sigma:
                #   Check if val_34 > 0! Since e1 = e2 + ell + 1 >= 4 + 3 + 1 = 8, (e1 + e2)/2 >= 6 > 4 >= sigma!!
                assert val_12 > 0, f"val_12={val_12} <= 0 at ell={ell}, e2={e2_val}, sigma={sigma}"
                assert val_34 > 0, f"val_34={val_34} <= 0 at ell={ell}, e2={e2_val}, sigma={sigma}"
                # Both strictly positive => all 4 factors lie in 1 + m_E subset O_E^x (strict 1-units, ZERO poles, ZERO exceptional zeros)!
                euler_checked += 1
    print(f"  PASS: Bad-prime constant term == 0 on Z/v^2Z; smoothing factors != 0; all 4 Euler factors strict 1-units on {euler_checked} instances (both V and V').")


if __name__ == "__main__":
    module1_bruhat_and_iwahori_containment()
    module2_locally_analytic_branching_and_weights()
    module3_small_slope_and_hecke_iwahori_klingen()
    module4_bad_primes_smoothing_and_dual_branch_euler()
    print("\nALL 4 MODULES PASSED (exit 0).")
    sys.exit(0)
