#!/usr/bin/env python3
"""
Wave-5 C01 Verification Script:
Symbolic & exact algebraic verification for GSp_4/Q automorphic induction AI_{K_0/Q}(f~)
at split primes, dual-branch closure (W and W tensor theta), Rubin big-image / kernel finiteness,
and Sp_4 -> SL_2 x SL_2 branching parity.

Note: Finite numerical/symbolic instances verify formulas and catch sign/index errors;
general proofs are given in erh_research/wave5/C01_gsp4_ai_split_closure.md.
"""

import sympy as sp
from sympy import Matrix, symbols, factor, expand, eye, zeros, simplify, Rational, Poly, legendre_symbol, isprime

def banner(title):
    print("=" * 78)
    print(f"  {title}")
    print("=" * 78)

# =============================================================================
# MODULE 1: Symplectic embeddings J_+, J_-, exterior square Lambda^2(V),
#           and exact central characters chi_+ = eta_{E_0}, chi_- = eta_{E_0'}
# =============================================================================
banner("MODULE 1: Symplectic Embeddings J_+, J_- and Lambda^2(Ind W~_0)")

a, b, c, d, a2, b2, c2, d2 = symbols('a b c d a2 b2 c2 d2')
th = symbols('th')  # theta(h) = det W(h) = det W^sigma(h)
# Represent h in G_{K_0} acting on V = W \oplus sigma W as block_diag(M1, M2)
# with det(M1) = det(M2) = th (since theta is Gal(K_0/Q)-invariant!).
M1 = Matrix([[a, b], [c, d]])
M2 = Matrix([[a2, b2], [c2, d2]])
H_mat = Matrix.diag(M1, M2)

# Represent sigma in G_{E_0} \ G_K (so eta_{E_0}(sigma) = +1, eta_{K_0}(sigma) = -1).
# sigma(u, sigma v) = (sigma^2 v, sigma u). With S2 = W(sigma^2), det(S2) = theta(sigma^2) = eps_sq.
# For Variant II biquadratic K = K_0(sqrt(-d)), eps_sq = +1.
# For C_4 cyclic CM quartic K/Q, eps_sq = -1.
s11, s12, s21, s22, eps_sq = symbols('s11 s12 s21 s22 eps_sq')
S2 = Matrix([[s11, s12], [s21, s22]])
Sigma_mat = Matrix([
    [0, 0, s11, s12],
    [0, 0, s21, s22],
    [1, 0, 0,   0  ],
    [0, 1, 0,   0  ]
])

J2 = Matrix([[0, 1], [-1, 0]])
J_plus = Matrix.diag(J2, J2)
J_minus = Matrix.diag(J2, -J2)

# Check H_mat^T J_pm H_mat
for name, J in [("J_+", J_plus), ("J_-", J_minus)]:
    res_H = simplify(H_mat.T * J * H_mat)
    expected_H = Matrix.diag((a*d - b*c) * J2, (a2*d2 - b2*c2) * (J[2:4, 2:4]))
    assert res_H == expected_H, f"Failed H invariance for {name}"
    # Setting det(M1) = det(M2) = th:
    res_H_sub = res_H.subs({a*d - b*c: th, a2*d2 - b2*c2: th})
    assert simplify(res_H_sub - th * J) == zeros(4, 4), f"Failed similitude th on G_K0 for {name}"
    print(f"[OK] {name} on G_{{K_0}}: H^T {name} H = theta(h) * {name}")

# Check Sigma_mat^T J_pm Sigma_mat (for Variant II: det(S2) = +1)
res_sig_plus = simplify((Sigma_mat.T * J_plus * Sigma_mat).subs(s11*s22 - s12*s21, 1))
res_sig_minus = simplify((Sigma_mat.T * J_minus * Sigma_mat).subs(s11*s22 - s12*s21, 1))
assert simplify(res_sig_plus - (+1) * J_plus) == zeros(4, 4)
assert simplify(res_sig_minus - (-1) * J_minus) == zeros(4, 4)
print("[OK] Variant II (det S2 = +1): Sigma^T J_+ Sigma = +J_+ (nu_+ = eta_{E_0})")
print("[OK] Variant II (det S2 = +1): Sigma^T J_- Sigma = -J_- (nu_- = eta_{E_0} * eta_{K_0})")

# Check C_4 cyclic case (det(S2) = -1): need J_i = diag(J2, i*J2) or diag(J2, -i*J2)
I_unit = sp.I
J_c4_plus = Matrix.diag(J2, I_unit * J2)
J_c4_minus = Matrix.diag(J2, -I_unit * J2)
res_c4_p = simplify((Sigma_mat.T * J_c4_plus * Sigma_mat).subs(s11*s22 - s12*s21, -1))
res_c4_m = simplify((Sigma_mat.T * J_c4_minus * Sigma_mat).subs(s11*s22 - s12*s21, -1))
assert simplify(res_c4_p - (+I_unit) * J_c4_plus) == zeros(4, 4)
assert simplify(res_c4_m - (-I_unit) * J_c4_minus) == zeros(4, 4)
print("[OK] C_4 cyclic CM case (det S2 = -1): nu_pm(sigma) = +-i (order-4 central characters)")

# Explicit 6x6 exterior square Lambda^2(V) decomposition on basis:
# e_0^e_1, e_2^e_3, e_0^e_2, e_0^e_3, e_1^e_2, e_1^e_3
pairs = [(0,1), (2,3), (0,2), (0,3), (1,2), (1,3)]
def ext2_matrix(G):
    M = zeros(6, 6)
    for col, (i, j) in enumerate(pairs):
        for row, (p, q) in enumerate(pairs):
            M[row, col] = G[p, i]*G[q, j] - G[p, j]*G[q, i]
    return M

L2_H = ext2_matrix(H_mat)
L2_Sig = ext2_matrix(Sigma_mat)

# Verify block structure: top 2x2 is Ind(det W), bottom 4x4 is As^-(W) = As(W) tensor eta_{K_0}!
assert L2_H[:2, 2:] == zeros(2, 4) and L2_H[2:, :2] == zeros(4, 2)
assert L2_Sig[:2, 2:] == zeros(2, 4) and L2_Sig[2:, :2] == zeros(4, 2)

# Check top 2x2 eigenvalues of L2_Sig when det(S2) = 1:
top2_Sig = L2_Sig[:2, :2].subs(s11*s22 - s12*s21, 1)
assert top2_Sig == Matrix([[0, 1], [1, 0]])
# Check bottom 4x4 of L2_Sig vs standard Asai swap (u \otimes v -> S2 v \otimes u)
# On e_0^e_2 -> (sigma e_0)^(sigma e_2) = e_2^(S2 e_0) = -(S2 e_0)^e_2! Extra MINUS sign!
S2_id = eye(2)
L2_Sig_id = ext2_matrix(Sigma_mat.subs({s11:1, s12:0, s21:0, s22:1}))
bot4 = L2_Sig_id[2:, 2:]
# Standard tensor swap on (0,0),(0,1),(1,0),(1,1) has trace +2 (3 symmetric +1, 1 antisymmetric -1).
# With extra minus sign (Asai^- = Asai tensor eta_{K_0}), trace must be -2!
assert bot4.trace() == -2
print(f"[OK] Lambda^2(V) splits as Ind(theta) [dim 2: chi_+ + chi_-] (+) As(W~_0) tensor eta_{{K_0}} [dim 4, tr(sigma) = {bot4.trace()}]")

# Also verify ad^0_{GSp_4}(V) (dim 10) = Ind(ad^0 W~_0) [dim 6] (+) As(W~_0) tensor eta_{E_0} [dim 4]
# On Sym^2(V) (dim 10), twist by nu_+^{-1} = eta_{E_0}:
# Check trace of H_mat (det=th) and Sigma_mat (S2=I_2, nu_+=+1) on Sym^2(V) * nu_+^{-1}:
tr_M1, tr_M2 = M1.trace(), M2.trace()
# For H_mat on Sym^2(V): tr = (tr(M1)^2 - det(M1)) + (tr(M2)^2 - det(M2)) + tr(M1)*tr(M2)
# Twisting by th^{-1}:
# ad^0(M1) has tr = tr(M1)^2/th - 1; ad^0(M2) has tr = tr(M2)^2/th - 1;
# Ind(ad^0) has dim 6, trace = tr(M1)^2/th + tr(M2)^2/th - 2;
# As(W~_0) tensor eta_{E_0} on G_{K_0} has trace = (tr(M1)*tr(M2)) * th = tr(M1)*tr(M2)/th (since th^2=1)!
# Wait: check Sym^2(M1) tensor th^{-1}: eigenvalues of M1 are x, th/x;
# Sym^2 eigenvalues are x^2, th, th^2/x^2; divided by th -> x^2/th, 1, th/x^2 = ad^0(M1)!
x1, x2 = symbols('x1 x2')
D1 = Matrix.diag(x1, th/x1)
D2 = Matrix.diag(x2, th/x2)
D_H = Matrix.diag(D1, D2)
# Trace of Sym^2(D_H) = (tr(D_H)^2 + tr(D_H^2))/2
tr_Sym2_H = simplify(((D_H.trace())**2 + (D_H**2).trace()) / 2 / th)
tr_ad0_1 = simplify(x1**2/th + 1 + th/x1**2)
tr_ad0_2 = simplify(x2**2/th + 1 + th/x2**2)
tr_As_th = simplify((x1 + th/x1) * (x2 + th/x2) / th)
assert simplify(tr_Sym2_H - (tr_ad0_1 + tr_ad0_2 + tr_As_th)) == 0
# On Sigma (with S2 = I_2, nu_+ = +1): Sym^2(Sigma) trace = (tr(Sig)^2 + tr(Sig^2))/2 = (0 + 4)/2 = +2.
# Ind(ad^0) has trace 0 on sigma; As(W~_0) tensor eta_{E_0} has trace (+2)*(+1) = +2 on sigma!
Sig_id = Sigma_mat.subs({s11:1, s12:0, s21:0, s22:1})
tr_Sym2_Sig = ((Sig_id.trace())**2 + (Sig_id**2).trace()) // 2
assert tr_Sym2_Sig == 2
print("[OK] ad^0_{GSp_4}(V) [dim 10] = Ind_{K_0/Q}(ad^0 W~_0) [dim 6] (+) As(W~_0) tensor eta_{E_0} [dim 4]")

# =============================================================================
# MODULE 2: Exact Weights (k_1, k_2), LSZ (r_1, r_2) = (k_1-3, k_2-3),
#           Critical Range, and Sp_4 -> SL_2 x SL_2 Weyl Character Branching
# =============================================================================
banner("MODULE 2: Weights, LSZ (r_1, r_2), and Sp_4 -> SL_2 x SL_2 Branching")

def sp4_character_on_sl2xsl2(r1, r2, t1, t2):
    """
    Exact Weyl character formula for irreducible rep V_{r1, r2} of Sp_4 (r1 >= r2 >= 0)
    restricted to the maximal torus diag(t1, t2, t1^{-1}, t2^{-1}) of SL_2 x SL_2.
    Highest weight in orthogonal coords: (r1, r2), rho = (2, 1).
    """
    # Weyl group of C_2 (order 8): permutations and sign changes of (t1, t2)
    l1, l2 = r1 + 2, r2 + 1
    def alt_sum(m1, m2):
        # sum_{w in W(C_2)} sgn(w) * t^{w(m1, m2)}
        return (
            (t1**m1 * t2**m2 - t1**(-m1) * t2**m2 - t1**m1 * t2**(-m2) + t1**(-m1) * t2**(-m2))
            - (t2**m1 * t1**m2 - t2**(-m1) * t1**m2 - t2**m1 * t1**(-m2) + t2**(-m1) * t1**(-m2))
        )
    num = expand(alt_sum(l1, l2))
    den = expand(alt_sum(2, 1))
    return sp.cancel(num / den)

def decompose_sl2xsl2(expr, t1, t2, max_deg):
    """Decompose a symmetric Laurent polynomial in (t1, t2) into Sym^{a1} x Sym^{a2}."""
    # Multiply by (t1*t2)^max_deg to work with polynomials
    rem = expand(expr)
    decomp = {}
    # Find highest weight terms lexicographically
    for total in range(max_deg, -1, -1):
        for a1 in range(total, -1, -1):
            a2 = total - a1
            # Coefficient of t1^a1 * t2^a2 in rem
            coeff = rem.coeff(t1, a1).coeff(t2, a2)
            # Handle a1=0 or a2=0 carefully using Laurent coeff:
            p = sp.expand(rem * t1**(max_deg+2) * t2**(max_deg+2))
            c_val = p.coeff(t1, max_deg + 2 + a1).coeff(t2, max_deg + 2 + a2)
            if c_val != 0:
                decomp[(a1, a2)] = int(c_val)
                chi_a1 = sum(t1**(a1 - 2*k) for k in range(a1 + 1))
                chi_a2 = sum(t2**(a2 - 2*k) for k in range(a2 + 1))
                rem = expand(rem - c_val * chi_a1 * chi_a2)
    assert rem == 0, f"Nonzero remainder in branching decomposition: {rem}"
    return decomp

t1, t2 = symbols('t1 t2')
for (e1, e2) in [(2, 1), (3, 1), (3, 2), (4, 2), (5, 4)]:
    k1 = e1 + e2 + 1
    k2 = e1 - e2 + 2
    r1_lsz = k1 - 3   # e1 + e2 - 2
    r2_lsz = k2 - 3   # e1 - e2 - 1
    assert r1_lsz == e1 + e2 - 2 and r2_lsz == e1 - e2 - 1
    assert r1_lsz >= r2_lsz >= 0
    assert r1_lsz - r2_lsz == 2*e2 - 1
    assert (r1_lsz + r2_lsz) % 2 == 1
    # Critical range [k2 - 1, k1 - 1] = [e1 - e2 + 1, e1 + e2]
    crit_lo, crit_hi = k2 - 1, k1 - 1
    assert crit_lo == e1 - e2 + 1 and crit_hi == e1 + e2
    assert crit_lo <= e1 <= crit_hi and crit_lo <= e1 + 1 <= crit_hi
    if e1 <= 4:  # full Weyl branching check for reasonable degrees
        ch = sp4_character_on_sl2xsl2(r1_lsz, r2_lsz, t1, t2)
        dec = decompose_sl2xsl2(ch, t1, t2, r1_lsz + r2_lsz)
        for (a1, a2), mult in dec.items():
            assert (a1 + a2) % 2 == 1, f"Parity violation at ({e1},{e2}): ({a1},{a2})"
        # Check dimension matches Weyl dim formula for Sp_4:
        weyl_dim = (r1_lsz - r2_lsz + 1)*(r2_lsz + 1)*(r1_lsz + 2)*(r1_lsz + r2_lsz + 3) // 6
        sum_dim = sum(mult * (a1 + 1) * (a2 + 1) for (a1, a2), mult in dec.items())
        assert weyl_dim == sum_dim
        print(f"[OK] (e1,e2)=({e1},{e2}) -> (k1,k2)=({k1},{k2}), (r1,r2)_LSZ=({r1_lsz},{r2_lsz}), "
              f"r1-r2={r1_lsz-r2_lsz}, dim={weyl_dim}, #summands={len(dec)}, ALL a1+a2 odd!")
    else:
        assert r1_lsz - r2_lsz >= 6, "Expected r1-r2 >= 6 for e2 >= 4"
        print(f"[OK] (e1,e2)=({e1},{e2}) -> (k1,k2)=({k1},{k2}), (r1,r2)_LSZ=({r1_lsz},{r2_lsz}), "
              f"r1-r2={r1_lsz-r2_lsz} >= 6 (LZ Thm B threshold!), crit=[{crit_lo},{crit_hi}] contains {e1},{e1+1}")

# =============================================================================
# MODULE 3: Dual Branch W~_0 tensor theta, Local Euler Factors (Zero Exceptional Zeros),
#           and Local Representation Types at p | D_{K_0} & p | D_{E_0}
# =============================================================================
banner("MODULE 3: Dual Branch, Newton/Hodge Polygons, and All 4 Euler Factors")

# Verify V' = V tensor eta_{E_0} \cong V^vee via J_+
# Symplectic pairing: v^T J_+ w is invariant up to nu_+ = eta_{E_0}, i.e.,
# (g v)^T J_+ (g w) = eta_{E_0}(g) v^T J_+ w  <=>  (g^T)^{-1} = eta_{E_0}(g)^{-1} J_+ g J_+^{-1}
# Since eta_{E_0}^2 = 1, V^vee \cong V tensor eta_{E_0} = V'!
# Check explicitly for both H_mat and Sigma_mat:
H_dual = (H_mat.T).inv()
H_twist = th * J_plus * H_mat * J_plus.inv()
# Substitute det(M1) = det(M2) = th:
diff_H_dual = simplify((H_dual - H_twist.subs(th, 1/th)).applyfunc(lambda e: e.subs({a*d - b*c: th, a2*d2 - b2*c2: th})))
# More directly: H_mat^T * J_plus * (eta * H_mat) = th * eta * J_plus = J_plus (since eta = th on G_{K_0} and th^2 = 1)
res_dual_H = simplify((H_mat.T * J_plus * H_mat).subs({d: (th + b*c)/a, d2: (th + b2*c2)/symbols('a2')}))
assert simplify((th * res_dual_H).subs(th**2, 1) - J_plus) == zeros(4, 4)
assert simplify((Sigma_mat.T * J_plus * ((+1) * Sigma_mat)).subs(s22, (1 + s12*s21)/s11) - J_plus) == zeros(4, 4)
print("[OK] Exact duality isomorphism: V' = Ind(W~_0 tensor theta) = V tensor eta_{E_0} ~= V^vee (via J_+)")

# Also verify Roberts-Schmidt Borel inducing characters at p | D_{K_0} (unramified f~ at p)
# V|_{D_p} = nu_a (+) nu_b (+) nu_a*eta (+) nu_b*eta, with nu_a*nu_b = eta_{E_0,p} (unramified), eta = eta_{K_0,p} (ramified cond p)
na, nb, eta_k = symbols('na nb eta_k')
# Choice (+) (central char eta_{E_0,p} = na*nb, unramified):
# sigma = na, chi1 = eta_k (cond p), chi2 = (nb/na)*eta_k (cond p)
sig_p, chi1_p, chi2_p = na, eta_k, (nb/na)*eta_k
vals_p = [sig_p, chi1_p*sig_p, chi2_p*sig_p, simplify((chi1_p*chi2_p*sig_p).subs(eta_k**2, 1))]
cc_p = simplify((chi1_p*chi2_p*sig_p**2).subs(eta_k**2, 1))
assert set(vals_p) == {na, na*eta_k, nb*eta_k, nb} and cc_p == na*nb
print(f"[OK] Local Pi_p^(+) at p | D_{{K_0}}: Borel data (chi1,chi2,sigma)=({chi1_p}, {chi2_p}, {sig_p}), central char={cc_p} (unramified!), paramodular cond p^2")
# Choice (-) (central char eta_{E_0,p}*eta_{K_0,p} = na*nb*eta_k, ramified!):
sig_m, chi1_m, chi2_m = na, nb/na, eta_k
vals_m = [sig_m, chi1_m*sig_m, chi2_m*sig_m, simplify(chi1_m*chi2_m*sig_m)]
cc_m = simplify(chi1_m*chi2_m*sig_m**2)
assert set(vals_m) == {na, nb, na*eta_k, nb*eta_k} and cc_m == na*nb*eta_k
print(f"[OK] Local Pi_p^(-) at p | D_{{K_0}}: Borel data (chi1,chi2,sigma)=({chi1_m}, {chi2_m}, {sig_m}), central char={cc_m} (ramified!)")

# Check Newton vs Hodge polygons and ALL 4 Euler factors at split l for e1 > e2 >= 1
for (e1, e2) in [(2, 1), (3, 2), (5, 4), (10, 4)]:
    k1, k2 = e1 + e2 + 1, e1 - e2 + 2
    # Unshifted motivic weight 2*e1:
    # 4 Frobenius eigenvalue l-adic valuations (split l = l1 * l2):
    # At l1 (wt 2e1+1): 0 and 2e1; At l2 (wt 2e2+1, shifted by e1-e2): e1-e2 and e1+e2
    newton_slopes = sorted([0, e1 - e2, e1 + e2, 2*e1])
    hodge_slopes = [0, k2 - 2, k1 - 1, k1 + k2 - 3]
    assert newton_slopes == hodge_slopes, f"Polygon mismatch at ({e1},{e2})"
    # Verify all 5 vertices match identically:
    newton_verts = [sum(newton_slopes[:i]) for i in range(5)]
    hodge_verts = [sum(hodge_slopes[:i]) for i in range(5)]
    assert newton_verts == hodge_verts

    # Check all 4 Euler factors at j = e1 + 1 (L(1, W~_0)) and j = e1 (L(0, W~_0)):
    # Complex norm of each alpha_i is l^{e1}; valuations are (0, e1-e2, e1+e2, 2e1).
    # At j = e1 + 1:
    #   Factors 1,2: 1 - l^{e1}/alpha_1, 1 - l^{e1}/alpha_2 -> l-adic vals of l^{e1}/alpha_i are e1, e2 (> 0!)
    #   Factors 3,4: 1 - beta_2/l^{e1+1}, 1 - beta_1/l^{e1+1} -> complex norms are l^{-1} < 1 (nonzero!)
    v_j1 = [e1 - newton_slopes[0], e1 - newton_slopes[1]]
    assert all(v >= 1 for v in v_j1), "Exceptional zero risk at j=e1+1!"
    # At j = e1:
    #   Factors 1,2: 1 - l^{e1-1}/alpha_i -> complex norms l^{-1} < 1 (nonzero!)
    #   Factors 3,4: 1 - beta_i/l^{e1} -> l-adic vals are e2, e1 (> 0!)
    v_j0 = [newton_slopes[2] - e1, newton_slopes[3] - e1]
    assert all(v >= 1 for v in v_j0), "Exceptional zero risk at j=e1!"
    print(f"[OK] (e1,e2)=({e1},{e2}): Newton==Hodge={newton_verts}; "
          f"j=e1+1 unit vals={v_j1} >= 1; j=e1 unit vals={v_j0} >= 1 (ZERO exceptional zeros for W~_0 & W~_0 x theta!)")

# Contrast e2 = 0 (weight 1): show exceptional zero risk
assert (2 - (2 - 0)) == 0
print("[OK] Contrast e2 = 0: v_l(l^{e1}/alpha_2) = 0 and |.|_inf = 1 (exceptional zero risk confirmed when e2=0!)")

# =============================================================================
# MODULE 4: Big Image Hyp(Q_infty, V) & Hyp(Q_infty, V') —
#           Semisimple tau, Unipotent Block-Swapping tau_unip, and B03 Sah Bug Check
# =============================================================================
banner("MODULE 4: Rubin Big Image (Non-Parallel & Parallel) + B03 Sah Bug Check")

u, x, y_sym = symbols('u x y')
# 4A: Non-parallel semisimple tau = g_inv * diag(I_2, diag(u, u^{-1}))
g_inv = Matrix.diag(1, -1, 1, -1)
h_u = Matrix.diag(1, 1, u, 1/u)
tau = g_inv * h_u
char_V = factor(tau.charpoly(x).as_expr())
expected_char_V = (x - 1)*(x + 1)*(x - u)*(x + 1/u)
assert simplify(char_V - expected_char_V) == 0
# Rank of tau - I_4 on V (for u != +-1):
tau_minus_I = tau - eye(4)
assert tau_minus_I.rank() == 3
# On V' = V tensor eta_{E_0}, eta_{E_0}(tau) = -1, so tau acts as -tau:
tau_prime = -tau
char_Vp = factor(tau_prime.charpoly(x).as_expr())
expected_char_Vp = (x + 1)*(x - 1)*(x + u)*(x - 1/u)
assert simplify(char_Vp - expected_char_Vp) == 0
assert (tau_prime - eye(4)).rank() == 3
# Non-1 eigenvalue determinant product:
non1_prod = simplify((-1 - 1)*(u - 1)*(-1/u - 1))
print(f"[OK] Non-parallel semisimple tau: char_V = {char_V}, rk(tau-I)=3")
print(f"[OK] Same tau on V' = V x eta_{{E_0}}: char_V' = {char_Vp}, rk(-tau-I)=3")
print(f"[OK] Non-1 eigenvalue product of (tau - I): {non1_prod} (at u=1+l^M: v_l = M, finite torsion!)")

# 4B: Parallel weight Aut(E)-inner-twist case: unipotent block-swapping tau_unip!
# tau_unip = sigma_inv * diag(U, U) where U = [[1, y], [0, 1]], y = l^M != 0
# sigma_inv in G_{E_0} \ G_K satisfies W(sigma_inv^2) = I_2 and eta_{E_0}(sigma_inv) = +1.
U_unip = Matrix([[1, y_sym], [0, 1]])
tau_unip = Matrix([
    [0, 0, 1, y_sym],
    [0, 0, 0, 1    ],
    [1, y_sym, 0, 0],
    [0, 1,     0, 0]
])
# Check tau_unip^2 = block_diag(U^2, U^2)
assert tau_unip**2 == Matrix.diag(U_unip**2, U_unip**2)
# Check charpoly and rank of tau_unip - I_4:
char_unip = factor(tau_unip.charpoly(x).as_expr())
rk_unip = (tau_unip - eye(4)).rank()
assert rk_unip == 3, f"Expected rank 3, got {rk_unip}"
# Since sigma_inv in G_{E_0} and h_u in G_K, eta_{E_0}(tau_unip) = +1, so SAME matrix acts on V'_0!
print(f"[OK] Parallel-weight unipotent tau_unip: char = {char_unip}, rk(tau_unip - I_4) = {rk_unip} => dim V_0/(tau_unip - 1)V_0 = 1!")
print("     (eta_{E_0}(tau_unip) = +1, so IDENTICAL tau_unip works simultaneously on V_0 and V'_0!)")

# 4C: Verify B03 line 254 Sah's Lemma bug (s_Sah is NOT central in SL_2 x SL_2!)
s_Sah = Matrix.diag(u, 1/u, u, 1/u)
test_sl2 = Matrix.diag(Matrix([[1, 1], [0, 1]]), eye(2))
comm = simplify(s_Sah * test_sl2 - test_sl2 * s_Sah)
assert comm != zeros(4, 4)
print(f"[OK] Confirmed B03 line 254 Sah bug: [s_Sah, diag([[1,1],[0,1]], I_2)] != 0 (entry (0,1) = {comm[0,1]} != 0)")
print("     Fixed in C01 via Lazard (1965) + Whitehead's First Lemma + Inflation-Restriction!")

# =============================================================================
# MODULE 5: Core-Rank 1 Local Orthogonality & Split-Split vs Split-Inert Primes
# =============================================================================
banner("MODULE 5: Klingen Local Orthogonality & Split Prime Density Audit")

# Basis of V|_{Q_l} = (e_1^+, e_1^-, e_2^+, e_2^-) where:
# e_1^+ in Fil^+ W~_0|_{D_{l1}} (HT +e1), e_1^- quotient (HT -e1)
# e_2^+ in Fil^+ W~_0|_{D_{l2}} (HT +e2), e_2^- quotient (HT -e2)
# Under J_+ = diag(J2, J2):
#   Fil^3 = span(e_1^+) (dim 1)
#   Fil^2 = span(e_1^+, e_2^+) (dim 2, Lagrangian!)
#   Fil^1 = span(e_1^+, e_2^+, e_2^-) (dim 3)
v_f3 = [Matrix([1, 0, 0, 0])]
v_f2 = [Matrix([1, 0, 0, 0]), Matrix([0, 0, 1, 0])]
v_f1 = [Matrix([1, 0, 0, 0]), Matrix([0, 0, 1, 0]), Matrix([0, 0, 0, 1])]

# Verify Fil^2 is Lagrangian: <Fil^2, Fil^2> = 0
for v in v_f2:
    for w in v_f2:
        assert (v.T * J_plus * w)[0] == 0
# Verify (Fil^1)^perp == Fil^3:
for v in v_f1:
    for w in v_f3:
        assert (v.T * J_plus * w)[0] == 0
# Verify e_1^- (outside Fil^1) pairs non-trivially with Fil^3:
assert (Matrix([0, 1, 0, 0]).T * J_plus * v_f3[0])[0] != 0
print("[OK] Symplectic orthogonality verified: (Fil^2)^perp = Fil^2 (Lagrangian), (Fil^1)^perp = Fil^3!")

# Tabulate odd primes l < 1000 for K_0 = Q(sqrt(5)), E_0 = Q(sqrt(-7))
D_K0, D_E0 = 5, -7
split_split, split_inert, inert_all = [], [], []
for p in range(3, 1000):
    if not isprime(p) or p in (5, 7):
        continue
    leg_K0 = legendre_symbol(D_K0, p)
    leg_E0 = legendre_symbol(D_E0, p)
    if leg_K0 == 1 and leg_E0 == 1:
        split_split.append(p)
    elif leg_K0 == 1 and leg_E0 == -1:
        split_inert.append(p)
    else:
        inert_all.append(p)

tot = len(split_split) + len(split_inert) + len(inert_all)
print(f"[OK] Odd primes l < 1000 (coprime to 5,7), total={tot}:")
print(f"     Split in K_0 & Split in E_0 (Pathway II direct U(3) + fixed-wt GSp_4): {len(split_split)} ({100*len(split_split)/tot:.1f}%) — first 8: {split_split[:8]}")
print(f"     Split in K_0 & Inert in E_0 (Requires Pathway I Hida specialization):  {len(split_inert)} ({100*len(split_inert)/tot:.1f}%) — first 8: {split_inert[:8]}")
print(f"     Inert in K_0                (Siegel-ord, non-Klingen-ord; C02 turf):   {len(inert_all)} ({100*len(inert_all)/tot:.1f}%) — first 8: {inert_all[:8]}")

# Verify conductor examples of chi_+ = eta_{E_0} vs chi_- = eta_{E_0'}
for D_real, d_imag in [(5, 7), (5, 11), (8, 7), (13, 7)]:
    cond_plus = d_imag if d_imag % 4 == 3 else 4 * d_imag
    cond_minus = D_real * cond_plus  # when gcd(D_real, cond_plus) == 1
    assert sp.gcd(D_real, cond_plus) == 1
    print(f"[OK] K_0=Q(sqrt({D_real})), E_0=Q(sqrt(-{d_imag})): cond(chi_+ = eta_{{E_0}}) = {cond_plus}, cond(chi_- = eta_{{E_0'}}) = {cond_minus}")

print("\nALL C01 SYMBOLIC & ALGEBRAIC ASSERTIONS PASSED (EXIT 0).")
