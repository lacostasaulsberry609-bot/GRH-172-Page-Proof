#!/usr/bin/env python3
"""
Exact pure-Python (stdlib-only) symbolic and finite-instance verification script for Wave-5 C03:
  1. Parity truth table (ch26/ch29/ch30) & G_3 conjugate-self-duality odd-weight lock (k = 2e+1).
  2. Exact symbolic multivariate-polynomial verification of the 4-summand Type II adjoint splitting
     in M_3 (ch29 eq:29:four-summand): M_3 = ad_G(W) + W + (W (x) theta) + eta_K.
  3. Exact linear-algebraic verification of GSp_4 adjoint root decomposition (ch30 eq:30:gsp4-r0),
     block weight sums (ixA = {0,2} vs {0,3}), and Eisenstein separation at e=1 vs e>=2.
  4. Exact rational Bernoulli numerator prime factors for B_{e+2} (even e in [2, 36]),
     illustrating the fixed-xi GSp_4 irregular-prime growth obstruction.

NOTE: Finite-instance and symbolic checks verify algebraic identities and explicit
examples; they do not replace the general proofs given in the report.
"""

from collections import defaultdict
from fractions import Fraction
import math


# ---------------------------------------------------------------------------
# Minimal exact multivariate polynomial over Q for symbolic matrix checks
# ---------------------------------------------------------------------------
class MPoly:
    """Exact polynomial in named variables over Q, represented as dict[monomial_tuple, Fraction]."""

    def __init__(self, terms=None):
        self.terms = {}
        if terms:
            for mon, coeff in terms.items():
                c = Fraction(coeff)
                if c != 0:
                    self.terms[mon] = c

    @staticmethod
    def const(c):
        return MPoly({(): Fraction(c)})

    @staticmethod
    def var(name):
        return MPoly({((name, 1),): Fraction(1)})

    def __add__(self, other):
        if not isinstance(other, MPoly):
            other = MPoly.const(other)
        out = defaultdict(Fraction, self.terms)
        for m, c in other.terms.items():
            out[m] += c
        return MPoly(out)

    def __radd__(self, other):
        return self.__add__(other)

    def __neg__(self):
        return MPoly({m: -c for m, c in self.terms.items()})

    def __sub__(self, other):
        if not isinstance(other, MPoly):
            other = MPoly.const(other)
        return self + (-other)

    def __rsub__(self, other):
        return MPoly.const(other) - self

    def __mul__(self, other):
        if not isinstance(other, MPoly):
            other = MPoly.const(other)
        out = defaultdict(Fraction)
        for m1, c1 in self.terms.items():
            for m2, c2 in other.terms.items():
                d = defaultdict(int, m1)
                for k, e in m2:
                    d[k] += e
                mon = tuple(sorted((k, e) for k, e in d.items() if e != 0))
                out[mon] += c1 * c2
        return MPoly(out)

    def __rmul__(self, other):
        return self.__mul__(other)

    def is_zero(self):
        return len(self.terms) == 0

    def __eq__(self, other):
        if not isinstance(other, MPoly):
            other = MPoly.const(other)
        return (self - other).is_zero()


def mat_mul(A, B):
    n, k, m = len(A), len(B), len(B[0])
    return [[sum((A[i][t] * B[t][j] for t in range(k)), MPoly.const(0)) for j in range(m)] for i in range(n)]


def mat_trans(A):
    return [[A[j][i] for j in range(len(A))] for i in range(len(A[0]))]


def mat_sub(A, B):
    return [[A[i][j] - B[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def mat_add(A, B):
    return [[A[i][j] + B[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def mat_scale(c, A):
    return [[c * A[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def mat_is_zero(A):
    return all(x.is_zero() for row in A for x in row)


# ---------------------------------------------------------------------------
# 1. Parity Truth Table & G_3 Odd-Weight Lock
# ---------------------------------------------------------------------------
def check_parity_and_g3_odd_weight_lock():
    print("=== 1. Parity Truth Table & G_3 Odd-Weight Lock ===")
    for psi_neg1 in (1, -1):
        for e_mod2 in (0, 1):
            Psi_c = ((-1) ** e_mod2) * psi_neg1
            branch = "Plus (Sha^1_+)" if Psi_c == 1 else "Minus (Sha^1_-)"
            if branch.startswith("Plus"):
                assert psi_neg1 == (-1) ** e_mod2
            else:
                assert psi_neg1 == (-1) ** (e_mod2 + 1)
            print(f"  psi(-1)={psi_neg1:+d}, e mod 2={e_mod2} => Psi(c)={Psi_c:+d} => {branch}")

    # Algebraic identity for conjugate-self-dual 3-tuple (a, b, c) with a + c = 2b:
    # outer spread a - c = 2(a - b) is ALWAYS even => weight k = (a - c) + 1 = 2(a - b) + 1 is ALWAYS odd.
    a, b = MPoly.var("a"), MPoly.var("b")
    c = 2 * b - a
    spread = a - c
    weight_k = spread + 1
    assert spread == 2 * (a - b)
    assert weight_k == 2 * (a - b) + 1
    # Check finite grid (a, b) with a > b:
    for a_v in range(1, 20):
        for b_v in range(-10, a_v):
            c_v = 2 * b_v - a_v
            k_v = (a_v - c_v) + 1
            assert k_v % 2 == 1 and k_v >= 3
    print("  Verified symbolically: conjugate-self-dual triple (a, b, 2b-a) has spread 2(a-b) => weight k = 2(a-b)+1 (ALWAYS ODD).")
    print("  For (e, 0, -e): spread = 2e, k = 2e+1 >= 3, det W(c) = -1 = (-1)^(2e+1).")
    print("  [PASS] Parity truth table & G_3 odd-weight lock verified.\n")


# ---------------------------------------------------------------------------
# 2. Symbolic Verification of Type II 4-Summand Adjoint Splitting (ch29)
# ---------------------------------------------------------------------------
def check_g3_typeii_four_summand_splitting():
    print("=== 2. Symbolic Verification of Type II 4-Summand Adjoint Splitting (ch29 eq:29:four-summand) ===")
    z, o, mo = MPoly.const(0), MPoly.const(1), MPoly.const(-1)
    J3 = [[z, z, o], [z, o, z], [o, z, z]]

    def theta_lie(X):
        return mat_scale(mo, mat_mul(mat_mul(J3, mat_trans(X)), J3))

    # Generic SL_2 matrix W parameterized by w00, w01, w10, w11 modulo (w00*w11 - w01*w10 - 1):
    # To check exact polynomial identities without rational functions, verify over SL_2 by writing
    #   W * Wadj = detW * I_2, so detW * ad(R)(X) = R * X * Radj!
    # Wait: on R = [[w00, 0, w01], [0, 1, 0], [w10, 0, w11]], when det(W) = 1,
    #   Rinv = [[w11, 0, -w01], [0, 1, 0], [-w10, 0, w00]].
    # Notice that R * X * Rinv is LINEAR in X and QUADRATIC in w_{ij}, and on entries (0,1),(2,1),(1,0),(1,2)
    # it is ONLY LINEAR in w_{ij} (because middle row/col of R and Rinv has 1 at (1,1) and 0 elsewhere)!
    # Let's check: R * X * Rinv at (0,1) = w00*x01 + w01*x21, independent of detW!!
    # At (1,2) = -w01*x10 + w00*x12!!
    w00, w01, w10, w11 = (MPoly.var(s) for s in ("w00", "w01", "w10", "w11"))
    W = [[w00, w01], [w10, w11]]
    Wc = [[mo, z], [z, o]]
    R = [[w00, z, w01], [z, o, z], [w10, z, w11]]
    Rinv = [[w11, z, -w01], [z, o, z], [-w10, z, w00]]

    # Check theta(R) = J3 * (Rinv)^T * J3 matches W(c) W W(c)^{-1} on {0,2} corner (valid when detW = 1)
    theta_R = mat_mul(mat_mul(J3, mat_trans(Rinv)), J3)
    W_conj_c = mat_mul(mat_mul(Wc, W), Wc)
    theta_R_corner = [[theta_R[0][0], theta_R[0][2]], [theta_R[2][0], theta_R[2][2]]]
    assert mat_is_zero(mat_sub(theta_R_corner, W_conj_c))

    # Generic 3x3 matrix X
    X = [[MPoly.var(f"x_{i}{j}") for j in range(3)] for i in range(3)]

    # Exact 4 projections & sections in M_3 (eq:29:four-summand):
    XA = [[X[0][0], z, X[0][2]], [z, z, z], [X[2][0], z, X[2][2]]]
    XC = [[z, z, z], [z, X[1][1], z], [z, z, z]]
    # Off-diagonal projections p_B(1) -> W and p_B(-1) -> W (x) theta:
    p1 = [X[0][1] + X[1][2], X[2][1] - X[1][0]]
    p2 = [X[0][1] - X[1][2], X[2][1] + X[1][0]]

    def sB1(v):
        return [[z, v[0], z], [-v[1], z, v[0]], [z, v[1], z]]

    def sBm1(v):
        return [[z, v[0], z], [v[1], z, -v[0]], [z, v[1], z]]

    half = MPoly.const(Fraction(1, 2))
    reconstructed = mat_add(mat_add(XA, XC), mat_add(mat_scale(half, sB1(p1)), mat_scale(half, sBm1(p2))))
    assert mat_is_zero(mat_sub(X, reconstructed)), "4-summand reconstruction identity failed!"

    # Check G_K-equivariance (exact polynomial identity for EVERY W in SL_2, even without substituting detW = 1!):
    adX = mat_mul(mat_mul(R, X), Rinv)
    p1_after = [adX[0][1] + adX[1][2], adX[2][1] - adX[1][0]]
    p2_after = [adX[0][1] - adX[1][2], adX[2][1] + adX[1][0]]
    Wp1 = [W[0][0] * p1[0] + W[0][1] * p1[1], W[1][0] * p1[0] + W[1][1] * p1[1]]
    Wp2 = [W[0][0] * p2[0] + W[0][1] * p2[1], W[1][0] * p2[0] + W[1][1] * p2[1]]
    assert p1_after[0] == Wp1[0] and p1_after[1] == Wp1[1]
    assert p2_after[0] == Wp2[0] and p2_after[1] == Wp2[1]

    # Check c-equivariance (ad(r(c))(X) = theta_Lie(X)):
    tX = theta_lie(X)
    p1_c = [tX[0][1] + tX[1][2], tX[2][1] - tX[1][0]]
    p2_c = [tX[0][1] - tX[1][2], tX[2][1] + tX[1][0]]
    # W(c) = diag(-1, 1); (W (x) theta)(c) = -W(c) = diag(1, -1)
    assert p1_c[0] == -p1[0] and p1_c[1] == p1[1]
    assert p2_c[0] == p2[0] and p2_c[1] == -p2[1]
    # Check XC transforms as eta_K (trivial on G_K, -1 on c):
    assert adX[1][1] == X[1][1] and tX[1][1] == -X[1][1]

    print("  Exact polynomial identity verified: X = s_A(p_A(X)) + (1/2)s_B(1)(p_B(1)(X)) + (1/2)s_B(-1)(p_B(-1)(X)) + p_C(X).")
    print("  Exact G_Q-equivariance verified: p_B(1) ~ W, p_B(-1) ~ W (x) theta, p_C ~ eta_K.")
    print("  [PASS] Type II 4-summand decomposition verified.\n")


# ---------------------------------------------------------------------------
# 3. GSp_4 Adjoint Root Decomposition, Purity Mismatch, & Eisenstein Separation
# ---------------------------------------------------------------------------
def check_gsp4_roots_purity_and_separation():
    print("=== 3. GSp_4 Adjoint Roots, Purity Mismatch, & Eisenstein Separation (ch30) ===")
    # Anti-diagonal skew-symmetric form J pairing (0,3) and (1,2)
    J = [
        [0, 0, 0, 1],
        [0, 0, 1, 0],
        [0, -1, 0, 0],
        [-1, 0, 0, 0],
    ]
    # Verify J^T = -J
    for i in range(4):
        for j in range(4):
            assert J[i][j] == -J[j][i]

    # Basis of sp_4 = {X in M_4 : X^T J + J X = 0}:
    # Explicitly construct all 10 standard root/Cartan basis matrices E_k and verify X^T J + J X = 0.
    def E(entries):
        M = [[0] * 4 for _ in range(4)]
        for i, j, val in entries:
            M[i][j] = val
        return M

    # Character labels & exponents in (alpha, Psi) for diag(alpha*Psi, Psi, alpha, 1):
    #   index 0: alpha^1 * Psi^1, HT = e+1, c = -1
    #   index 1: alpha^0 * Psi^1, HT = e,   c = +1
    #   index 2: alpha^1 * Psi^0, HT = 1,   c = -1
    #   index 3: alpha^0 * Psi^0, HT = 0,   c = +1
    char_exp = [(1, 1), (0, 1), (1, 0), (0, 0)]
    c_eigs = [-1, 1, -1, 1]

    basis_spec = [
        ("Cartan h_1", [(0, 0, 1), (3, 3, -1)]),
        ("Cartan h_2", [(1, 1, 1), (2, 2, -1)]),
        ("+w_Psi (even)", [(0, 2, 1), (1, 3, 1)]),
        ("-w_Psi (even)", [(2, 0, 1), (3, 1, 1)]),
        ("+w_alpha (odd)", [(0, 1, 1), (2, 3, -1)]),
        ("-w_alpha (odd)", [(1, 0, 1), (3, 2, -1)]),
        ("+w_theta (odd)", [(0, 3, 1)]),
        ("-w_theta (odd)", [(3, 0, 1)]),
        ("+w_beta (odd)", [(1, 2, 1)]),
        ("-w_beta (odd)", [(2, 1, 1)]),
    ]
    assert len(basis_spec) == 10

    even_roots = 0
    odd_roots = 0
    cartan_cnt = 0
    for name, entries in basis_spec:
        M = E(entries)
        # Verify M^T J + J M == 0
        for i in range(4):
            for j in range(4):
                s = sum(M[k][i] * J[k][j] + J[i][k] * M[k][j] for k in range(4))
                assert s == 0, f"{name} not in sp_4!"
        # Verify all nonzero entries carry the SAME character ratio and c-eigenvalue
        ratios = set()
        cvals = set()
        for i, j, _ in entries:
            da = char_exp[i][0] - char_exp[j][0]
            dp = char_exp[i][1] - char_exp[j][1]
            ratios.add((da, dp))
            cvals.add(c_eigs[i] * c_eigs[j])
        assert len(ratios) == 1 and len(cvals) == 1
        da, dp = next(iter(ratios))
        cv = next(iter(cvals))
        if (da, dp) == (0, 0):
            cartan_cnt += 1
        elif cv == 1:
            even_roots += 1
        else:
            odd_roots += 1
        print(f"    {name:16s} support={[(i,j) for i,j,_ in entries]!s:18s} alpha^{da:+d} Psi^{dp:+d}  c={cv:+d}")

    assert cartan_cnt == 2 and even_roots == 2 and odd_roots == 6

    # Check purity mismatch of {0,2}+{1,3} vs {0,3}+{1,2} blocks for e >= 1
    for e_val in range(1, 20):
        ht = [e_val + 1, e_val, 1, 0]
        mult_wt = ht[0] + ht[3]  # e + 1
        assert ht[0] + ht[2] == e_val + 2 != mult_wt
        assert ht[1] + ht[3] == e_val != mult_wt
        assert ht[0] + ht[3] == mult_wt and ht[1] + ht[2] == mult_wt
    print("  Verified: even-root blocks {0,2}+{1,3} (ixA=![0,2]) have sums (e+2, e) != e+1 (killed by purity).")
    print("  Verified: odd-root blocks  {0,3}+{1,2}              have sums (e+1, e+1) == e+1 (NOT killed by purity).")

    # Siegel weight formula {0, k2-2, k1-1, k1+k2-3} = {0, 1, e, e+1} => k1 = e+1, k2 = 3;
    # dominant regular condition k1 >= k2 >= 3 <=> e >= 2.
    for e_val in (2, 3, 5, 10, 50):
        for p_val in (5, 7, 11, 13):
            # ch30 lem:30:sp4-cong-num L280-285:
            lhs = (3 * math.sqrt(p_val) + 1) * (p_val ** ((e_val + 1) / 2)) + p_val ** e_val + p_val + 1
            rhs = p_val ** (e_val + 1)
            assert lhs < rhs, f"Separation failed at e={e_val}, p={p_val}"

    e1_failures = []
    e1_first_pass = None
    for p_val in (5, 7, 11, 13, 17, 19, 23):
        lhs = (3 * math.sqrt(p_val) + 1) * p_val + p_val + p_val + 1
        rhs = p_val ** 2
        if lhs >= rhs:
            e1_failures.append((p_val, round(lhs, 2), rhs))
        elif e1_first_pass is None:
            e1_first_pass = (p_val, round(lhs, 2), rhs)
    assert [x[0] for x in e1_failures] == [5, 7, 11, 13]
    assert e1_first_pass[0] == 17
    print(f"  Eisenstein separation e>=2, p>=5: PASSED all tested (e,p).")
    print(f"  Eisenstein separation e=1: FAILS for p in {[x[0] for x in e1_failures]} (p=5: {e1_failures[0][1]} > {e1_failures[0][2]}); first holds at p={e1_first_pass[0]}.")
    print("  [PASS] GSp_4 roots, purity, and separation verified.\n")


# ---------------------------------------------------------------------------
# 4. Exact Bernoulli Numbers B_{e+2} & Prime Factors (Fixed-xi GSp_4 Obstruction)
# ---------------------------------------------------------------------------
def bernoulli_upto(N):
    """Exact Bernoulli numbers B_0, ..., B_N via Akiyama-Tanigawa / recurrence."""
    B = [Fraction(0)] * (N + 1)
    B[0] = Fraction(1)
    for m in range(1, N + 1):
        s = Fraction(0)
        for k in range(m):
            s += math.comb(m + 1, k) * B[k]
        B[m] = -s / (m + 1)
    return B


def is_probable_prime(n):
    if n < 2:
        return False
    small = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    for p in small:
        if n == p:
            return True
        if n % p == 0:
            return False
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    # Deterministic Miller-Rabin for n < 3.317e24 using first 12 primes
    for a in small:
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(s - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True


def pollard_rho(n):
    if n % 2 == 0:
        return 2
    for c in range(1, 200):
        x, y, d = 2, 2, 1
        while d == 1:
            x = (x * x + c) % n
            y = (y * y + c) % n
            y = (y * y + c) % n
            d = math.gcd(abs(x - y), n)
        if d != n:
            return d
    raise RuntimeError(f"Factorization failed for {n}")


def factor_int(n):
    res = defaultdict(int)
    def rec(m):
        if m == 1:
            return
        if is_probable_prime(m):
            res[m] += 1
            return
        for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
            if m % p == 0:
                res[p] += 1
                rec(m // p)
                return
        d = pollard_rho(m)
        rec(d)
        rec(m // d)
    rec(n)
    return dict(res)


def check_bernoulli_bad_prime_growth():
    print("=== 4. Finite-Instance Check: Irregular Prime Factors of num(B_{e+2}) (Fixed-xi GSp_4 Obstruction) ===")
    B = bernoulli_upto(42)
    assert B[12] == Fraction(-691, 2730)
    records = []
    for e_val in range(2, 42, 2):
        m = e_val + 2
        num = abs(B[m].numerator)
        facs = factor_int(num)
        # Verify exact factorization product
        prod = 1
        for p, k in facs.items():
            assert is_probable_prime(p)
            prod *= p ** k
        assert prod == num
        max_p = max(facs.keys()) if facs else 1
        log_num = math.log(num) if num > 1 else 0.0
        stirling_log = math.log(2) + math.lgamma(m + 1) - m * math.log(2 * math.pi)
        records.append((e_val, m, max_p, log_num, stirling_log))
        if m in (12, 22, 32, 36, 40, 42):
            print(f"  e={e_val:2d}, m=e+2={m:2d}: max prime l | num(B_m) = {max_p:<22d} | log(num)={log_num:6.2f}, log|B_m|_asymp={stirling_log:6.2f}")

    # Confirm 691 | num(B_12) and huge primes (> 10^19 at m=36, > 10^21 at m=42) across mod-5 and mod-3 classes
    assert 691 in factor_int(abs(B[12].numerator))
    m36 = [r for r in records if r[1] == 36][0]
    m42 = [r for r in records if r[1] == 42][0]
    assert m36[2] > 10**19 and m36[2] % 5 in (2, 3)  # inert in Q(sqrt(5))
    assert m42[2] > 10**21 and m42[2] % 5 in (1, 4)  # split in Q(sqrt(5))
    print(f"  Verified: l = 691 | num(B_12); m=36 max prime = {m36[2]} (mod 5 = {m36[2]%5}, inert in Q(sqrt(5)));")
    print(f"            m=42 max prime = {m42[2]} (mod 5 = {m42[2]%5}, split in Q(sqrt(5))).")
    print("  [PASS] Fixed-xi Bernoulli numerator bad-prime growth confirmed on finite instances (m <= 42).\n")


if __name__ == "__main__":
    check_parity_and_g3_odd_weight_lock()
    check_g3_typeii_four_summand_splitting()
    check_gsp4_roots_purity_and_separation()
    check_bernoulli_bad_prime_growth()
    print("ALL C03 VERIFICATION CHECKS PASSED (exit 0).")
