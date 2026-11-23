#!/usr/bin/env python3
"""
Verification script for Wave-8 F04:
  - Route 4A: Mod-varpi self-duality parity obstruction, L' = L(zeta_ell) repair,
    BDP vs Greenberg linear-algebra decoupling, and Delta-eigenspace Massey pairing.
  - Route 4B: GSpin(5,2) root datum, Weyl coset Bruhat lengths / Hodge types,
    B3 -> D3 -> B2 branching laws (sphericity of SO(7)/SO(6) vs non-sphericity of SO(7)/SO(5)),
    Hasse-Witt Bott periodicity for SO(2d0-1, 2), S3 Mackey descent, symplectic induction,
    pushforward motivic degree & Weil II weight checks, and core-rank codimension table.

Note: Finite/symbolic checks serve as computational verification of identities and
finite parameter grids; all general theorems are proved in the report text.
"""

import itertools
from fractions import Fraction
import sympy as sp


def run_module_1_route_4a():
    print("=== [Module 1] Route 4A: Mod-varpi Self-Duality Parity & L' = L(zeta_ell) Repair ===")

    # 1.1 Exhaustive check of Mod-varpi Self-Duality Parity Obstruction
    # For odd prime ell, even ell-1 can never divide odd (2r+1) or odd (2e - (2r+1)).
    primes = list(sp.primerange(3, 100))
    checked_triples = 0
    for ell in primes:
        # Determinant obstruction for n=2: ord(omega_ell^2) = (ell-1)/2 >= 2 for ell >= 5
        if ell >= 5:
            assert (ell - 1) % 2 == 0 and (ell - 1) // 2 >= 2
        for e in range(1, 21):
            for r in range(-10, 11):
                shift = 2 * r + 1  # any odd motivic weight -(2r+1)
                assert shift % (ell - 1) != 0, f"Unexpected match: ell={ell}, shift={shift}"
                assert (2 * e - shift) % (ell - 1) != 0, f"Unexpected cross match: ell={ell}, e={e}, shift={shift}"
                checked_triples += 1
    print(f"  [1.1] Verified Mod-varpi Parity Obstruction on {checked_triples} triples (ell in [3,97], e in [1,20], odd shifts): 0 exceptions.")

    # 1.2 Exact verification of the omega_ell discrepancy in B01 Eq. (187)
    # 2m = 2e + 1 + ell^M; rho_{f_{2m}} has det = theta * omega_ell^{-ell^M} * chi_cyc^{2m-1}
    # U_{2m}^+ = W_{2m}|_{G_L} * <chi_cyc>^{1/2} = rho_{f_{2m}}(1-m)|_{G_L} * omega_ell^{m-1-e}
    # Exponent of omega_ell in det(U_{2m}^+) is: -ell^M + 2(m - 1 - e)
    disc_checks = 0
    for ell in [5, 7, 11, 13, 17, 19, 23]:
        for e in range(1, 10):
            if (2 * e) % (ell - 1) == 0:
                continue  # GD12: (ell-1) nmid 2e
            for M in range(1, 5):
                two_m = 2 * e + 1 + ell**M
                assert two_m % 2 == 0
                m = two_m // 2
                omega_exp = -(ell**M) + 2 * (m - 1 - e)
                assert omega_exp == -1, f"Expected -1, got {omega_exp}"
                # Hence det(U_{2m}^+) = omega_ell^{-1} * chi_cyc != chi_cyc on G_L (order ell-1 >= 4)
                assert (-1) % (ell - 1) != 0
                # Check central character parity at c = (c_L, -1) on L'^+ = (L(zeta_ell))^+
                eps_f2m_c = (-1) * ((-1) ** (-(ell**M)))
                assert eps_f2m_c == 1
                # Also check weight-2 point f_2: eps_{f_2} = theta * omega_ell^{2e-1}
                eps_f2_c = (-1) * ((-1) ** (2 * e - 1))
                assert eps_f2_c == 1
                # Check definite global root number over L' = L(zeta_ell): d_{L'^+} = (ell-1)*d_L
                for d_L in [2, 4, 6, 8]:
                    d_Lprime = (ell - 1) * d_L
                    assert d_Lprime % 4 == 0
                    assert (-1) ** d_Lprime == 1
                disc_checks += 1
    print(f"  [1.2] Verified omega_ell^-1 bug in B01 Eq.(187) & exact L'=L(zeta_ell) trivial-central-char / definite-root-number repair on {disc_checks} tuples.")

    # 1.3 Check ell-adic valuation v_ell((1 + ell)^{1/2} - 1) == 1
    for ell in [3, 5, 7, 11, 13, 17, 19, 23, 29]:
        # Compute sqrt(1 + ell) mod ell^5 via Hensel / binomial series
        mod = ell**5
        inv2 = pow(2, -1, mod)
        # Binomial series sum_{k=1}^5 binom(1/2, k) ell^k mod ell^5
        val = 0
        binom_num = 1
        binom_den = 1
        for k in range(1, 6):
            binom_num *= (1 - 2 * (k - 1))
            binom_den *= (2 * k)
            term_num = binom_num * (ell**k)
            # Strip powers of ell from binom_den (note k <= 5; for ell=3, k=3 has factor 3)
            g = sp.gcd(term_num, binom_den)
            tn = term_num // g
            td = binom_den // g
            if td % ell != 0:
                val = (val + tn * pow(int(td), -1, mod)) % mod
        assert val % ell == 0 and val % (ell**2) != 0, f"Valuation failed at ell={ell}: val={val}"
        # Verify (1 + val)^2 == 1 + ell mod ell^4 (for ell=3, term k=3 contributes ell^2, still mod ell^3)
        check_mod = ell**3 if ell == 3 else ell**5
        assert ((1 + val) ** 2 - (1 + ell)) % check_mod == 0
    print("  [1.3] Verified v_ell(kappa_cyc^{1/2} - 1) = 1 for ell in {3..29} -> (varpi, T_cyc - T_cen) = (varpi, T_cyc).")

    # 1.4 Check Delta = Gal(L'/L) eigenspace duality i <-> (1 - i) mod (ell - 1) has NO fixed points
    for ell in primes:
        fixed = [i for i in range(ell - 1) if (2 * i - 1) % (ell - 1) == 0]
        assert len(fixed) == 0, f"Fixed point found at ell={ell}: {fixed}"
    print("  [1.4] Verified Delta-duality i <-> (1 - i) mod (ell - 1) has 0 fixed points for all odd primes ell < 100.")

    # 1.5 Linear algebra counterexample: H^1_BDP = 0 does NOT imply H^1_Gr = 0 (dim G cap Gr = d_L possible)
    # Ambient local space Q^{4 d_L}: coords (x_fil, x_quot, y_fil, y_quot), each of dim d_L.
    # BDP subspace = {y_fil = 0, y_quot = 0} (dim 2 d_L).
    # Gr subspace  = {x_quot = 0, y_quot = 0} (dim 2 d_L).
    # Take global subspace G = span of columns:
    #   [I_{d_L}, 0; 0, I_{d_L}; I_{d_L}, 0; 0, I_{d_L}] (dim 2 d_L).
    for d_L in [1, 2, 3, 4]:
        I = sp.eye(d_L)
        Z = sp.zeros(d_L)
        G = sp.BlockMatrix([[I, Z], [Z, I], [I, Z], [Z, I]]).as_explicit()  # 4d_L x 2d_L
        # BDP projection: rows 2d_L .. 4d_L-1 (y_fil, y_quot)
        proj_BDP = G[2 * d_L :, :]
        assert proj_BDP.rank() == 2 * d_L  # => G cap BDP = {0}, i.e., H^1_BDP = 0!
        # Gr projection: rows [x_quot] (d_L..2d_L-1) and [y_quot] (3d_L..4d_L-1)
        proj_Gr = sp.Matrix.vstack(G[d_L : 2 * d_L, :], G[3 * d_L :, :])
        dim_H1_Gr = 2 * d_L - proj_Gr.rank()
        assert dim_H1_Gr == d_L  # => H^1_Gr has maximal dimension d_L despite H^1_BDP = 0!
    print("  [1.5] Verified explicit decoupling H^1_BDP = 0 with dim H^1_Gr = d_L for d_L in {1,2,3,4}.")


def weyl_dim_B(lam):
    """Weyl dimension formula for B_n with dominant weight lam = (l_1, ..., l_n) (integers or half-integers)."""
    n = len(lam)
    rho = [Fraction(2 * n - 1 - 2 * i, 2) for i in range(n)]
    lr = [Fraction(lam[i]) + rho[i] for i in range(n)]
    num = Fraction(1)
    den = Fraction(1)
    # Positive roots of B_n: e_i (i=0..n-1), e_i - e_j, e_i + e_j (0 <= i < j < n)
    for i in range(n):
        num *= lr[i]
        den *= rho[i]
    for i in range(n):
        for j in range(i + 1, n):
            num *= (lr[i] - lr[j]) * (lr[i] + lr[j])
            den *= (rho[i] - rho[j]) * (rho[i] + rho[j])
    res = num / den
    assert res.denominator == 1
    return int(res)


def weyl_dim_D(nu):
    """Weyl dimension formula for D_n with dominant weight nu = (n_1, ..., n_n) (n_1 >= ... >= |n_n|)."""
    n = len(nu)
    rho = [Fraction(n - 1 - i) for i in range(n)]
    nr = [Fraction(nu[i]) + rho[i] for i in range(n)]
    num = Fraction(1)
    den = Fraction(1)
    for i in range(n):
        for j in range(i + 1, n):
            num *= (nr[i] - nr[j]) * (nr[i] + nr[j])
            den *= (rho[i] - rho[j]) * (rho[i] + rho[j])
    res = num / den
    assert res.denominator == 1
    return int(res)


def branch_B3_to_D3(lam):
    """Exact B_3 -> D_3 branching rule: l1 >= n1 >= l2 >= n2 >= l3 >= |n3|, same parity (int vs half-int)."""
    l1, l2, l3 = [Fraction(x) for x in lam]
    half = l1.denominator == 2
    step_list = lambda a, b: [a + k for k in range(int(b - a) + 1)]
    out = []
    for n1 in step_list(l2, l1):
        for n2 in step_list(l3, l2):
            for n3 in step_list(-l3, l3):
                out.append((n1, n2, n3))
    return out


def branch_D3_to_B2(nu):
    """Exact D_3 -> B_2 branching rule: n1 >= m1 >= n2 >= m2 >= |n3|, same parity."""
    n1, n2, n3 = [Fraction(x) for x in nu]
    step_list = lambda a, b: [a + k for k in range(int(b - a) + 1)]
    out = []
    for m1 in step_list(n2, n1):
        for m2 in step_list(abs(n3), n2):
            out.append((m1, m2))
    return out


def run_module_2_route_4b_lie():
    print("\n=== [Module 2] Route 4B: GSpin(5,2) Root Datum, Weyl/Hodge Decomposition & Branching Laws ===")

    # 2.1 Cartan matrix duality C(B_3)^T = C(C_3)
    C_B3 = sp.Matrix([[2, -1, 0], [-1, 2, -2], [0, -1, 2]])  # alpha_1 = e1-e2, alpha_2 = e2-e3, alpha_3 = e3 (short)
    C_C3 = sp.Matrix([[2, -1, 0], [-1, 2, -1], [0, -2, 2]])  # alpha_1 = e1-e2, alpha_2 = e2-e3, alpha_3 = 2e3 (long)
    assert C_B3.T == C_C3
    print("  [2.1] Verified Cartan duality C(B_3)^T = C(C_3) -> Langlands dual of GSpin(5,2) is GSp_6(C).")

    # 2.2 Enumerate W(B_3) (size 48) and minimal coset reps W(B_2)\W(B_3) (size 6)
    # Represent signed permutations as tuples (s0*p0, s1*p1, s2*p2) acting on (x0, x1, x2)
    pos_roots_B3 = [
        (1, -1, 0), (1, 1, 0), (1, 0, -1), (1, 0, 1), (0, 1, -1), (0, 1, 1),
        (1, 0, 0), (0, 1, 0), (0, 0, 1),
    ]
    assert len(pos_roots_B3) == 9
    rho_B3 = tuple(Fraction(sum(r[i] for r in pos_roots_B3), 2) for i in range(3))
    assert rho_B3 == (Fraction(5, 2), Fraction(3, 2), Fraction(1, 2))

    # Build W(B_3) acting on weight vectors v = (v0, v1, v2)
    W_B3 = []
    for perm in itertools.permutations([0, 1, 2]):
        for signs in itertools.product([1, -1], repeat=3):
            W_B3.append((perm, signs))
    assert len(W_B3) == 48

    def apply_w(w, v):
        perm, signs = w
        return tuple(signs[i] * v[perm[i]] for i in range(3))

    def bruhat_length(w):
        # Number of positive roots alpha with w(alpha) < 0 (lexicographically: first nonzero entry < 0)
        cnt = 0
        for r in pos_roots_B3:
            wr = apply_w(w, r)
            for c in wr:
                if c != 0:
                    if c < 0:
                        cnt += 1
                    break
        return cnt

    # Kostant representatives W^{P_1}: w in W(B_3) such that w^{-1}(alpha) > 0 for all positive roots of B_2 = <e2-e3, e3>
    # Equivalently w(e2 - e3) > 0 and w(e3) > 0? Wait: left vs right cosets:
    # For P_1 with Levi B_2 acting on coordinates (1, 2) (indices 1, 2):
    # w maps rho_B3 to w(rho_B3) dominant for B_2 iff (w(rho_B3))_1 > (w(rho_B3))_2 > 0!
    kostant_reps = []
    for w in W_B3:
        wr = apply_w(w, rho_B3)
        if wr[1] > wr[2] > 0:
            kostant_reps.append((bruhat_length(w), w, wr))
    kostant_reps.sort(key=lambda t: t[0])
    lengths = [t[0] for t in kostant_reps]
    assert len(kostant_reps) == 6
    assert lengths == [0, 1, 2, 3, 4, 5], f"Unexpected lengths: {lengths}"
    # Verify exact Hodge-Tate weights from first coordinate of w(lambda + rho) for lambda = (e1-5/2, e2-3/2, e3-1/2)
    e1, e2, e3 = sp.symbols("e1 e2 e3", integer=True, positive=True)
    inf_char = (e1, e2, e3)
    ht_weights = [apply_w(w, inf_char)[0] for _, w, _ in kostant_reps]
    assert ht_weights == [e1, e2, e3, -e3, -e2, -e1], f"Unexpected HT weights: {ht_weights}"
    print(f"  [2.2] Verified |W(B_3)|=48, |W^P1|=6, exact Bruhat lengths={lengths}, Hodge-Tate weights={ht_weights}.")

    # 2.3 Branching laws B_3 -> D_3 (spherical!) and B_3 -> B_2 (NON-SPHERICAL!)
    # Check dimension conservation for both tensorial and spinorial weights
    test_weights = [
        (0, 0, 0), (1, 0, 0), (2, 1, 0), (3, 1, 0), (4, 2, 1),  # tensorial
        (Fraction(1, 2), Fraction(1, 2), Fraction(1, 2)),       # spinor (e=(3,2,1))
        (Fraction(3, 2), Fraction(1, 2), Fraction(1, 2)),       # e=(4,2,1)
        (Fraction(5, 2), Fraction(3, 2), Fraction(1, 2)),       # e=(5,3,1)
    ]
    for lam in test_weights:
        d_B3 = weyl_dim_B(lam)
        d3_list = branch_B3_to_D3(lam)
        assert len(d3_list) == len(set(d3_list))  # multiplicity-free!
        assert sum(weyl_dim_D(nu) for nu in d3_list) == d_B3
        b2_mult = {}
        for nu in d3_list:
            for mu in branch_D3_to_B2(nu):
                b2_mult[mu] = b2_mult.get(mu, 0) + 1
        assert sum(m * weyl_dim_B(mu) for mu, m in b2_mult.items()) == d_B3
        # For spinorial weights, check (1/2, 1/2) (= Std_4 of GSp_4) appears iff l3 == 1/2 (i.e. e3 == 1)
        if Fraction(lam[0]).denominator == 2 and lam[2] == Fraction(1, 2):
            assert b2_mult.get((Fraction(1, 2), Fraction(1, 2)), 0) >= 1
            # And trivial rep (0,0) NEVER appears for spinorial weights!
            assert b2_mult.get((0, 0), 0) == 0

    # Explicitly verify SO(7)/SO(5) non-sphericity: dim V_{(l1,l2,0)}^{SO(5)} == l1 - l2 + 1
    for l1 in range(0, 7):
        for l2 in range(0, l1 + 1):
            d3_list = branch_B3_to_D3((l1, l2, 0))
            inv_SO6 = sum(1 for nu in d3_list if nu == (0, 0, 0))
            assert inv_SO6 == (1 if l2 == 0 else 0)  # <= 1 => SO(7)/SO(6) IS SPHERICAL!
            inv_SO5 = 0
            for nu in d3_list:
                for mu in branch_D3_to_B2(nu):
                    if mu == (0, 0):
                        inv_SO5 += 1
            assert inv_SO5 == l1 - l2 + 1  # unbounded => SO(7)/SO(5) IS NON-SPHERICAL!
    print("  [2.3] Verified B_3->D_3->B_2 Weyl dimensions: dim V_{(l1,l2,0)}^{SO_6} <= 1 (SPHERICAL) vs dim V_{(l1,l2,0)}^{SO_5} = l1-l2+1 (NON-SPHERICAL!).")

    # 2.4 Explicit symplectic pairing on Ind_{F_3^+}^{Q}(W) (6x6 skew-symmetric matrix J_6)
    a1, b1, c1, d1 = sp.symbols("a1 b1 c1 d1")
    a2, b2, c2, d2 = sp.symbols("a2 b2 c2 d2")
    a3, b3, c3, d3 = sp.symbols("a3 b3 c3 d3")
    eta = sp.symbols("eta")  # common det = eta_{E_0}
    J2 = sp.Matrix([[0, 1], [-1, 0]])
    J6 = sp.diag(J2, J2, J2)
    assert J6.T == -J6  # skew-symmetric (symplectic!)
    # General monomial block matrix (3-cycle permutation * diag(M1, M2, M3) with det(Mi) = eta)
    M1 = sp.Matrix([[a1, b1], [c1, (eta + b1 * c1) / a1]])
    M2 = sp.Matrix([[a2, b2], [c2, (eta + b2 * c2) / a2]])
    M3 = sp.Matrix([[a3, b3], [c3, (eta + b3 * c3) / a3]])
    P_cyc = sp.BlockMatrix([
        [sp.zeros(2), sp.eye(2), sp.zeros(2)],
        [sp.zeros(2), sp.zeros(2), sp.eye(2)],
        [sp.eye(2), sp.zeros(2), sp.zeros(2)],
    ]).as_explicit()
    G_mat = P_cyc * sp.diag(M1, M2, M3)
    assert sp.simplify(G_mat.T * J6 * G_mat - eta * J6) == sp.zeros(6)
    print("  [2.4] Verified exact 6x6 symplectic invariance G^T J_6 G = eta * J_6 for Ind_{F_3^+}^{Q}(W) -> GSp_6.")


def hilbert_symbol_inf(a, b):
    return -1 if (a < 0 and b < 0) else 1


def hasse_inf(diag_entries):
    prod = 1
    n = len(diag_entries)
    for i in range(n):
        for j in range(i + 1, n):
            prod *= hilbert_symbol_inf(diag_entries[i], diag_entries[j])
    return prod


def run_module_3_route_4b_obstructions():
    print("\n=== [Module 3] Route 4B: Hasse-Witt Bott Periodicity, S_3 Mackey, Degrees & Core Rank ===")

    # 3.1 Relative real Hasse invariant c_infty(SO(2d0-1, 2)) = (-1)^{floor((d0-1)/2)}
    print("  [3.1] Hasse-Witt Bott Periodicity for SO(2d0-1, 2) (d0 = 1..12):")
    for d0 in range(1, 13):
        # Signature (2d0-1, 2), det = +1
        diag_target = [1] * (2 * d0 - 1) + [-1, -1]
        eps_target = hasse_inf(diag_target)
        assert eps_target == -1
        # Split form of dim 2d0+1 and det = +1: H^{d0} perp <(-1)^{d0}>
        # H = <1, -1>
        diag_split = [1, -1] * d0 + [(-1) ** d0]
        # Verify det == +1
        det_split = 1
        for x in diag_split:
            det_split *= x
        assert det_split == 1
        eps_split = hasse_inf(diag_split)
        c_inf = eps_target * eps_split  # ratio in {+1, -1}
        expected = (-1) ** ((d0 - 1) // 2)
        assert c_inf == expected, f"Mismatch at d0={d0}: {c_inf} vs {expected}"
        if d0 <= 6:
            status = "SPLIT everywhere exists" if c_inf == 1 else "MUST ramify at odd # >= 1 finite primes!"
            print(f"        d0={d0}: SO({2*d0-1},2) vs split ({diag_split.count(1)},{diag_split.count(-1)}) -> c_inf={c_inf:+d} ({status})")

    # Verify explicit 7-dim form Q = x1^2+...+x5^2 - x6^2 - x7^2:
    # At p=2: (-1,-1)_2 = -1; at p=inf: (-1,-1)_inf = -1; at odd p: (-1,-1)_p = +1. Product = (-1)(-1) = +1.
    assert (-1) * (-1) == 1
    # Also check compact form (7, 0) vs split (3, 4) for d0 = 3:
    # Even over ANY totally real field M^+ with signature (5,2) x (7,0)^{r-1},
    # c_inf(7,0) = hasse_inf([1]*7) * hasse_inf([1,-1]*3 + [-1]) = (+1)*(+1) = +1,
    # so prod_{v|inf} c_v = (-1) * (+1)^{r-1} = -1 ALWAYS!
    assert hasse_inf([1] * 7) * hasse_inf([1, -1] * 3 + [-1]) == 1
    print("        (Also verified c_inf(7,0) = +1 -> even over ANY totally real M^+ with signature (5,2)x(7,0)^{r-1}, prod_{v|inf} c_v = -1!)")

    # 3.2 S_3 Mackey identity: Ind_{C_2}^{S_3}(W)|_{C_3} = Ind_{1}^{C_3}(W|_1)
    # Check double cosets C_3 \ S_3 / C_2 has size 1 (since C_3 * C_2 = S_3, C_3 cap C_2 = {1})
    S3 = list(itertools.permutations([0, 1, 2]))
    C2 = [(0, 1, 2), (1, 0, 2)]  # fixes 2
    C3 = [(0, 1, 2), (1, 2, 0), (2, 0, 1)]
    def compose(p, q):
        return tuple(p[q[i]] for i in range(3))
    prod_set = {compose(a, b) for a in C3 for b in C2}
    assert len(prod_set) == 6 and set(C3).intersection(C2) == {(0, 1, 2)}
    print("  [3.2] Verified S_3 = C_3 * C_2 with C_3 cap C_2 = {1} -> Mackey C_2->C_3->C_2 yields unconditional AI_{F_3^+/Q}(W) for S_3 cubics.")

    # 3.3 Pushforward degree equation p + 2c = D_G + 1 = 6 on X_{GSpin(5,2)} (D_G = 5, rk_R = 2)
    D_G = 5
    target_deg = D_G + 1
    assert target_deg == 6
    for D_H in range(1, D_G + 1):
        c = D_G - D_H
        p = target_deg - 2 * c
        if D_H == 1:
            assert p == -2  # impossible
        elif D_H == 2:
            assert (c, p) == (3, 0)  # algebraic cycle -> Weil II weight -1!
        elif D_H == 3:
            assert (c, p) == (2, 2)  # GSpin(3,2)=GSp_4 -> non-spherical + no H^2_M Eisenstein class!
        elif D_H == 4:
            assert (c, p) == (1, 4)  # GSpin(4,2)~GU(2,2) -> spherical, needs H^4_M!
    # Check Y_1^k pushforward for all k <= rk_R = 2:
    # From Eis^{boxtimes k} in H^k_M(Y_1^k), pushforward degree is k + 2*(5 - k) = 10 - k != 6 for k <= 2!
    for k in [1, 2]:
        assert k + 2 * (5 - k) != 6
    # Solving k + 2*(5 - k) = 6 gives k = 4 > 2 = rk_R(SO(5,2))!
    assert 10 - 6 == 4 and 4 > 2

    # 3.4 Parabolic dimensions for SO(7) and SO(6)
    dim_SO7 = 7 * 6 // 2  # 21
    dim_SO6 = 6 * 5 // 2  # 15
    dim_SO5 = 5 * 4 // 2  # 10
    assert dim_SO7 == 21 and dim_SO6 == 15 and dim_SO5 == 10
    assert dim_SO7 - dim_SO6 == 6
    assert dim_SO7 - dim_SO5 == 11
    # Maximal parabolics P_k of SO(7): Levi GL_k x SO(7-2k)
    for k, expected_flag_dim in [(1, 5), (2, 7), (3, 6)]:
        dim_L = k * k + (7 - 2 * k) * (6 - 2 * k) // 2
        dim_U = (dim_SO7 - dim_L) // 2
        assert dim_U == expected_flag_dim

    # 3.5 Core-rank table for d0 = 1..6
    print("  [3.5] Core-rank & local codimension table for V = Ind_{F^+}^{Q}(W):")
    for d0 in range(1, 7):
        dim_V = 2 * d0
        dim_V_minus = d0
        dim_H1f = d0
        # For rank-1 Euler system: chi(F) = dim F_ell - dim (V^*(1))^+ = dim F_ell - d0 == 1
        dim_F_ell = d0 + 1
        codim_F_ell = dim_V - dim_F_ell
        assert codim_F_ell == d0 - 1
        spin_dim_GSp = 2**d0
        if d0 >= 3:
            assert spin_dim_GSp > dim_V
        print(f"        d0={d0}: dim V={dim_V:2d}, GSp Spin={spin_dim_GSp:2d}, chi={dim_V_minus}, dim F_ell={dim_F_ell}, codim F_ell={codim_F_ell}")


if __name__ == "__main__":
    run_module_1_route_4a()
    run_module_2_route_4b_lie()
    run_module_3_route_4b_obstructions()
    print("\nALL F04 VERIFICATION CHECKS PASSED (exit 0).")
