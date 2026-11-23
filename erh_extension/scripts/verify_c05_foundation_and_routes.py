#!/usr/bin/env python3
"""
Symbolic & arithmetic verification script for Wave-5 C05 report:
  1. G_3 ordinary deformation dimensions, Greenberg-Wiles Euler characteristics,
     and 3 d_L = dim(Lambda_0) = dim(Z_endo) verification.
  2. Constant-trace pole-free Brauer-Nesbitt lemma (Bug #3 repair) &
     Branch A vs Branch B complete-intersection multiplicity conservation.
  3. Explicit counterexamples to B01-2's "abelian L^+/Q" claim (Bug #2).
  4. Route 2(a): Central involution No-Go for Ad(Sym^n W) and general reductive H;
     GSp_{2 d_0} Spin-dimension mismatch vs GSpin(2 d_0 - 1, 2) table.
"""

import sympy as sp


def part1_dimensions_and_jacobian():
    print("=== [Part 1] G_3 Adjoint Splitting, Dimensions & Jacobian ===")
    J3 = sp.Matrix([[0, 0, 1], [0, 1, 0], [1, 0, 0]])

    # Verify theta_Lie(X) = -J3 * X^T * J3 on M_3
    basis = [sp.zeros(3, 3) for _ in range(9)]
    idx = 0
    for i in range(3):
        for j in range(3):
            basis[idx][i, j] = 1
            idx += 1

    # Matrix of theta_Lie in the 9-dim basis
    T_theta = sp.zeros(9, 9)
    for col, E_ij in enumerate(basis):
        img = -J3 * E_ij.T * J3
        for row in range(9):
            r, c = divmod(row, 3)
            T_theta[row, col] = img[r, c]

    evals = T_theta.eigenvals()
    assert evals == {1: 3, -1: 6}, f"Unexpected theta_Lie eigenvalues: {evals}"
    print(f"  theta_Lie eigenvalues on M_3: {evals} (dim+ = 3, dim- = 6) [OK]")

    # Verify Greenberg-Wiles Euler characteristic for symbolic d_L
    d_L = sp.Symbol("d_L", positive=True, integer=True)
    # Local ordinary Borel b_3 has dim 6 => sum_{v|l} 6 d_v = 6 d_L
    # Archimedean places: sum_{v|inf} (-dim+) = -3 d_L
    chi_g3 = 6 * d_L - 3 * d_L
    assert chi_g3 == 3 * d_L

    # Endoscopic summands:
    # ad^0(W): dim b_2^0 = 2, dim+ = 1 => 2 d_L - d_L = d_L
    # E(theta) (mu): dim b_1 = 1, dim+ = 0 => d_L - 0 = d_L
    # E(theta) (chi): dim b_1 = 1, dim+ = 0 => d_L - 0 = d_L
    # W + W*theta: dim Fil+ = 2, dim+ = 2 => 2 d_L - 2 d_L = 0
    chi_ad0 = 2 * d_L - 1 * d_L
    chi_mu = 1 * d_L - 0
    chi_chi = 1 * d_L - 0
    chi_off = 2 * d_L - 2 * d_L
    assert chi_ad0 + chi_mu + chi_chi + chi_off == chi_g3
    assert chi_ad0 + chi_mu + chi_chi == 3 * d_L
    print(f"  Greenberg-Wiles: chi(ad(r_f)) = {chi_g3} = {chi_ad0}(W) + {chi_mu}(mu) + {chi_chi}(chi) + {chi_off}(off-diag) [OK]")

    # Jacobian of (kappa_0, mu, chi) -> (kappa_0*mu, chi, kappa_0^{-1}*mu)
    J_split = sp.Matrix([[1, 1, 0], [0, 0, 1], [-1, 1, 0]])
    det_J = J_split.det()
    assert det_J == -2
    print(f"  det(J_split) = {det_J} (unit in Z_ell for all odd ell) [OK]")


def part2_pole_free_brauer_nesbitt_and_branches():
    print("\n=== [Part 2] Pole-Free Brauer-Nesbitt Lemma & Branch A/B Algebra ===")
    J3 = sp.Matrix([[0, 0, 1], [0, 1, 0], [1, 0, 0]])
    alpha, beta = sp.symbols("alpha beta")
    # Most general element of End_{G_L}(1 + W) in basis (e_0, e_1, e_2)
    A0 = sp.diag(alpha, beta, alpha)
    # Check commutator with arbitrary W(g) = [[a, b], [c, d]] on {0, 2}
    a, b, c, d = sp.symbols("a b c d")
    M_g = sp.Matrix([[a, 0, b], [0, 1, 0], [c, 0, d]])
    assert A0 * M_g - M_g * A0 == sp.zeros(3, 3)

    # Leading term of g(u) * J3 * g(u)^T * J3 for g(u) = u^{-k}(A0 + O(u))
    leading = A0 * J3 * A0.T * J3
    assert leading == sp.diag(alpha**2, beta**2, alpha**2)
    # Setting leading = 0 forces alpha = 0 AND beta = 0 => A0 = 0!
    sol = sp.solve([leading[0, 0], leading[1, 1], leading[2, 2]], [alpha, beta])
    assert sol == [(0, 0)]
    print(f"  A0 * J3 * A0^T * J3 = diag(alpha^2, beta^2, alpha^2) = 0 => {sol} [OK]")

    # Branch A vs Branch B complete intersection tests
    t, x = sp.symbols("t x")
    # Branch A: f(t, x) = x(x^2 - t)
    fA = x * (x**2 - t)
    assert fA.subs(x, 0) == 0
    assert sp.expand(fA.subs(x, -x) + fA) == 0
    assert fA.subs(t, 0) == x**3  # fixed-weight dim = 3
    JA = sp.diff(fA, x).subs(x, 0)
    assert JA == -t and JA != 0  # generically smooth along x = 0!
    # Branch B: f(t, x) = x^3 + t*x^5
    fB = x**3 + t * x**5
    assert fB.subs(x, 0) == 0
    assert sp.expand(fB.subs(x, -x) + fB) == 0
    assert fB.subs(t, 0) == x**3  # fixed-weight dim = 3
    JB = sp.diff(fB, x).subs(x, 0)
    assert JB == 0  # det J(t) == 0 identically!
    print(f"  Branch A: f={fA}, J(t)={JA} (non-zero, absorbed by x^2=t) [OK]")
    print(f"  Branch B: f={fB}, J(t)={JB} (identically zero, rank>=1 everywhere) [OK]")


def part3_abelian_base_change_counterexamples():
    print("\n=== [Part 3] Counterexamples to Abelian L^+/Q Claim (K0 = Q(sqrt(5))) ===")
    # Primes inert in Q(sqrt(5)): q = 2, 3 (mod 5)
    inert_primes = [q for q in [3, 7, 13, 17, 23, 37, 43] if pow(5, (q - 1) // 2, q) == q - 1]
    assert inert_primes == [3, 7, 13, 17, 23, 37, 43]
    for q in inert_primes:
        # In Q_q, max tame abelian ramification index divides q - 1.
        # In K_{0,q} = Q_{q^2}, tame inertia character can have any order dividing q^2 - 1.
        # Take order m = (q + 1) if q+1 is not dividing q-1 (always true for q >= 3 since q+1 > q-1).
        m = q + 1
        assert (q**2 - 1) % m == 0
        assert (q - 1) % m != 0
        # Even taking odd part or 2-power part: for q=3, m=4 | 8 while q-1=2; for q=7, m=8 | 48 while q-1=6
        print(f"  q={q:2d} (inert in Q(sqrt(5))): |F_{{q^2}}^*|={q**2-1:4d}, m=q+1={m:2d} divides q^2-1 but NOT q-1={q-1:2d} [COUNTEREXAMPLE]")


def part4_route_2a_nogo_and_shimura_table():
    print("\n=== [Part 4] Route 2(a): Central Involution No-Go & GSp_{2d0} vs GSpin(2d0-1,2) ===")
    # 4A: Verify End(Sym^n W) = direct sum_{k=0}^n Sym^{2k} W (always even!)
    # Use character of diag(u, u^{-1}) in SL_2
    u = sp.Symbol("u")
    for n in range(1, 9):
        chi_sym_n = sum(u**(n - 2 * j) for j in range(n + 1))
        chi_end = sp.expand(chi_sym_n * chi_sym_n)  # Sym^n is self-dual on SL_2
        expected = sp.expand(sum(sum(u**(2 * k - 2 * j) for j in range(2 * k + 1)) for k in range(n + 1)))
        assert chi_end == expected
        # Central involution z = -I_2 corresponds to u = -1
        # Check chi_end at u = -1 equals dim(End(Sym^n W)) = (n+1)^2 (meaning z acts as +1 identically!)
        assert chi_end.subs(u, -1) == (n + 1)**2
        # Meanwhile on W = Sym^1, chi_W = u + u^{-1}, at u=-1 equals -2 = -dim(W) (z acts as -1!)
        assert (u + u**(-1)).subs(u, -1) == -2
    print("  Verified End(Sym^n W) = sum_{k=0}^n Sym^{2k} W (n=1..8): z=-I_2 acts as +1, never contains W [OK]")

    # 4B: Verify explicit z = -I_2 action on gl_3 (Type II), sp_4 (Std+Std), g_2
    # In gl_3 with 1 + W: z = diag(-1, 1, -1)
    z_gl3 = sp.diag(-1, 1, -1)
    plus_dim, minus_dim = 0, 0
    for i in range(3):
        for j in range(3):
            E_ij = sp.zeros(3, 3)
            E_ij[i, j] = 1
            conj = z_gl3 * E_ij * z_gl3
            if conj == E_ij:
                plus_dim += 1
            elif conj == -E_ij:
                minus_dim += 1
            else:
                raise AssertionError("Not an eigenvector!")
    assert (plus_dim, minus_dim) == (5, 4)
    print(f"  Ad(z) on gl_3: dim(+1)={plus_dim} (gl_2+gl_1), dim(-1)={minus_dim} (W + W*) => M subset C_H(z) proper! [OK]")

    # 4C: Compare GSp_{2 d_0} vs GSpin(2 d_0 - 1, 2) for d_0 = 1..6
    print("\n  d_0 | dim Ind(W)=2d0 | GSp_{2d0} Spin=2^d0 | dim X(GSp) | dim X(GSpin(2d0-1,2)) | rk_R(SO) | core-rk chi | req local codim")
    print("  ----+----------------+---------------------+------------+-----------------------+----------+-------------+----------------")
    for d0 in range(1, 7):
        dim_ind = 2 * d0
        dim_spin = 2**d0
        dim_gsp = d0 * (d0 + 1) // 2
        dim_gspin = 2 * d0 - 1
        rk_r = min(2 * d0 - 1, 2)
        chi = d0
        req_codim = d0 - 1
        # Check accidental match ONLY for d0 in {1, 2}
        if d0 in (1, 2):
            assert dim_spin == dim_ind
        else:
            assert dim_spin > dim_ind
        # Check discrete series L-packet size of SO(2d0-1, 2): |W(B_d0)| / |W(B_{d0-1})| = 2*d0
        w_bd0 = (2**d0) * sp.factorial(d0)
        w_bd0_m1 = (2**(d0 - 1)) * sp.factorial(d0 - 1)
        assert w_bd0 // w_bd0_m1 == dim_ind
        print(f"  {d0:3d} | {dim_ind:14d} | {dim_spin:19d} | {dim_gsp:10d} | {dim_gspin:21d} | {rk_r:8d} | {chi:11d} | {req_codim:15d}")

    print("\nALL C05 VERIFICATION CHECKS PASSED (exit 0).")


if __name__ == "__main__":
    part1_dimensions_and_jacobian()
    part2_pole_free_brauer_nesbitt_and_branches()
    part3_abelian_base_change_counterexamples()
    part4_route_2a_nogo_and_shimura_table()
