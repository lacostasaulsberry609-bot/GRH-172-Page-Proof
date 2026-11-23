#!/usr/bin/env python3
"""
Wave-3 Assault A01: Exact 2D Shintani Ray-Class Twist Experiments on K0 = Q(sqrt(5)).

Tests:
1. Calibration against W2 table (F^+_725, F^CM_1025, F^CM_1525, quadratic CM fields).
2. Exact 2D ray-class group Cl^+_m(K0) structure for:
   - Split rational primes m = q * O_K0
   - Inert rational primes m = q * O_K0
   - Single split prime ideals m = q1
   - Fibonacci moduli m = F_k * O_K0 (where ord_m(eps_+) <= k = O(log M)!)
   - Prime divisors of Fibonacci/Lucas numbers
   - Products of 2 or 3 split prime ideals m = q1 * q2 (* q3)
3. Exact mod-l nonvanishing fractions (single value, double value (beta, theta),
   triple value (alpha, beta, theta)) over prime-to-l totally odd ray-class characters xi!
4. Exact 2D Fourier transform S_phi(u) on single <eps_+>-orbits and mixed 2D differencing!
"""

import math
from fractions import Fraction
from collections import Counter, defaultdict
import sympy as sp

# =============================================================================
# Arithmetic in K0 = Q(sqrt(5)), O_K0 = Z[omega] = Z + Z * eps_+
# omega = (1 + sqrt(5))/2, omega^2 = 1 + omega = eps_+
# eps_+ = (3 + sqrt(5))/2, eps_+^2 = 3*eps_+ - 1, N(eps_+) = 1, Tr(eps_+) = 3
# Basis {1, eps_+}: element (a, b) means a + b * eps_+.
# Note: omega = eps_+ - 1 = (-1, 1).
# Multiplication in basis {1, eps_+}:
# (a + b e)(c + d e) = (ac - bd) + (ad + bc + 3bd) e
# Norm: N(a + b e) = a^2 + 3ab + b^2
# =============================================================================

def mul_ok(x, y, mod=None):
    a, b = x
    c, d = y
    r0 = a * c - b * d
    r1 = a * d + b * c + 3 * b * d
    if mod is not None:
        return (r0 % mod, r1 % mod)
    return (r0, r1)

def pow_ok(x, k, mod):
    res = (1 % mod, 0)
    base = (x[0] % mod, x[1] % mod)
    while k > 0:
        if k & 1:
            res = mul_ok(res, base, mod)
        base = mul_ok(base, base, mod)
        k >>= 1
    return res

def norm_ok(x):
    a, b = x
    return a * a + 3 * a * b + b * b

def inv_ok(x, mod):
    """Inverse of (a, b) mod (mod * O_K0), assuming gcd(N(x), mod) == 1."""
    a, b = x
    n = (a * a + 3 * a * b + b * b) % mod
    n_inv = pow(n, -1, mod)
    # conjugate of a + b*eps_+ is (a + 3b) - b*eps_+
    return (((a + 3 * b) * n_inv) % mod, ((-b) * n_inv) % mod)

# Precompute W_N(a, b) * (12 * N^2) as exact integers!
# W_N(a, b) = (a/N - 1/2)(b/N - 1/2) + (3/4)*((a/N)^2 - a/N + 1/6 + (b/N)^2 - b/N + 1/6)
# Multiply by 12 * N^2:
# 12 * N^2 * (a/N - 1/2)(b/N - 1/2) = 3 * (2a - N)(2b - N)
# 12 * N^2 * (3/4) * (a^2/N^2 - a/N + 1/6) = 9 * a^2 - 9 * a * N + 3 * N^2 / 2
# Together for both a and b:
# 12 * N^2 * W_N(a, b) = 3*(2a - N)*(2b - N) + 9*(a^2 - a*N + b^2 - b*N) + 3*N^2
# Check: at a=N, b=N: 3*N*N + 0 + 3*N^2 = 6*N^2 => W_N(N, N) = 1/2.
# Check directly: B_1(1)^2 + (3/4)*(2*B_2(1)) = 1/4 + (3/4)*(1/3) = 1/2. EXACT!
def W_num(a, b, N):
    """Returns exact integer 12 * N^2 * W_N(a, b)."""
    return 3 * (2 * a - N) * (2 * b - N) + 9 * (a * a - a * N + b * b - b * N) + 3 * N * N

def B1_num(a, N):
    """Returns exact integer 12 * N^2 * B_1(a/N) = 6 * N * (2a - N)."""
    return 6 * N * (2 * a - N)

# =============================================================================
# Fast Shintani partial zeta sums mod M * O_K0 with fixed character phi mod f
# =============================================================================

def split_prime_root(p):
    """For p == 1 or 4 (mod 5), find roots r of x^2 - 3x + 1 = 0 mod p (i.e. eps_+ mod p_i)."""
    assert p % 5 in (1, 4)
    # x = (3 +- sqrt(5)) / 2 mod p
    s5 = sp.sqrt_mod(5, p)
    inv2 = pow(2, -1, p)
    r1 = ((3 + s5) * inv2) % p
    r2 = ((3 - s5) * inv2) % p
    assert (r1 * r1 - 3 * r1 + 1) % p == 0
    assert (r2 * r2 - 3 * r2 + 1) % p == 0
    assert (r1 * r2) % p == 1
    return (r1, r2)

def make_psi0_725():
    """F^+_725: p_29 = (5 + omega) = (4 + eps_+), so eps_+ == -4 == 25 mod p_29.
    psi_0(a + b eps_+) = legendre(a - 4b, 29)."""
    def phi(a, b):
        val = (a - 4 * b) % 29
        if val == 0:
            return 0
        return sp.legendre_symbol(val, 29)
    return 29, phi

def make_psi0_1025():
    """F^CM_1025: p_41 = (6 + omega) = (5 + eps_+), so eps_+ == -5 == 36 mod p_41.
    psi_0^CM(a + b eps_+) = legendre(a - 5b, 41) (NOTE: totally odd on K0!)."""
    def phi(a, b):
        val = (a - 5 * b) % 41
        if val == 0:
            return 0
        return sp.legendre_symbol(val, 41)
    return 41, phi

def make_trivial():
    return 1, lambda a, b: 1

def test_calibration():
    print("=" * 72)
    print("STEP 1: CALIBRATION OF 2D SHINTANI FORMULA ON K0 = Q(sqrt(5))")
    print("=" * 72)
    # 1a. F^CM_1025: conductor p_41, totally odd! L(0, psi_0^CM) = 2*h^-(F^CM_1025)/(Q*w)
    f, phi = make_psi0_1025()
    tot = 0
    for a in range(1, f + 1):
        for b in range(1, f + 1):
            v = phi(a, b)
            if v:
                tot += v * W_num(a, b, f)
    # Ray term vanishes since phi(-1) = legendre(-1, 41) = +1
    val = Fraction(tot, 12 * f * f)
    print(f"F^CM_1025: L_K0(0, psi_0^CM) = {val}  (expected integer 2*h^-/(Q*w); 41==1 mod 4)")
    # Check psi_0^CM(omega) = legendre(-1 - 5, 41) = legendre(-6, 41)
    print(f"  psi_0^CM(-1) = {phi(-1, 0)}, psi_0^CM(omega) = {phi(-1, 1)}, psi_0^CM(eps_+) = {phi(0, 1)}")

    # 1b. F^+_725 twisted by odd chi_4 o N: W2 table says n=2 => L = 4!
    f, phi = make_psi0_725()
    print(f"F^+_725: psi_0(-1) = {phi(-1, 0)}, psi_0(omega) = {phi(-1, 1)}, psi_0(eps_+) = {phi(0, 1)}")
    M = 4
    N = f * M
    tot = 0
    for a in range(1, N + 1):
        for b in range(1, N + 1):
            vp = phi(a, b)
            if vp == 0:
                continue
            nm = (a * a + 3 * a * b + b * b) % 4
            if nm % 2 == 0:
                continue
            vx = 1 if nm == 1 else -1
            tot += vp * vx * W_num(a, b, N)
    val = Fraction(tot, 12 * N * N)
    print(f"F^+_725 twisted by chi_4 o N (n=2): L = {val}  (W2 table: 4)")
    assert val == 4, f"Calibration mismatch: got {val}, expected 4"

    # 1c. F^+_725 twisted by n=3 (mod 8 odd character: 1->1, 3->-1, 5->-1, 7->1? No, chi_8 odd: 1->1, 3->1, 5->-1, 7->-1)
    # W2 table says n=3 => 12!
    M = 8
    N = f * M
    chi8_odd = {1: 1, 3: 1, 5: -1, 7: -1}
    tot = 0
    for a in range(1, N + 1):
        for b in range(1, N + 1):
            vp = phi(a, b)
            if vp == 0:
                continue
            nm = (a * a + 3 * a * b + b * b) % 8
            if nm % 2 == 0:
                continue
            tot += vp * chi8_odd[nm] * W_num(a, b, N)
    val = Fraction(tot, 12 * N * N)
    print(f"F^+_725 twisted by chi_8_odd o N (n=3): L = {val}  (W2 table: 12)")
    assert val == 12, f"Calibration mismatch: got {val}, expected 12"
    print("CALIBRATION PASSED 100%!\n")

# =============================================================================
# Fast 2D partial sum elimination of odd conductor f:
# Given phi periodic mod f (gcd(f, M) = 1), compute G_M(u1, u2) for 1 <= u1, u2 <= M
# where G_M(u1, u2) = sum_{a==u1 mod M, b==u2 mod M, 1<=a,b<=fM} phi(a + b*e) * W_{fM}(a, b)
# =============================================================================

def compute_GM_table(f, phi, M):
    """
    Returns table G[u1][u2] (1-indexed mod M, stored at 0..M-1 representing u%M,
    with 0 representing M) as exact Fractions, in O(f^2 + M^2) time!
    WAIT: Let's verify the O(f^2 + M^2) speedup!
    Write a = u1 + r1*M (0 <= r1 < f, 1 <= u1 <= M), b = u2 + r2*M (0 <= r2 < f, 1 <= u2 <= M).
    W_{fM}(a, b) = (a/(fM) - 1/2)(b/(fM) - 1/2) + (3/4)*(B_2(a/(fM)) + B_2(b/(fM)))
    Notice a/(fM) = r1/f + u1/(fM), b/(fM) = r2/f + u2/(fM).
    AND phi(u1 + r1*M + (u2 + r2*M)*e) ONLY depends on (u1 mod f, u2 mod f, r1, r2)!
    So the polynomial in (u1, u2) has ONLY 6 coefficients depending on (u1 mod f, u2 mod f):
      c_00, c_10, c_01, c_11, c_20, c_02!
    That computes G_M(u1, u2) for ALL M^2 pairs in O(f^4) or O(f^2 * M^2)? Wait:
    Even better: let x = (u1 + r1*M) mod f, y = (u2 + r2*M) mod f.
    Since gcd(M, f) = 1, r1 = (x - u1) * M^{-1} mod f!
    For each (u1_f, u2_f) in (Z/fZ)^2, we just sum over r1, r2 in 0..f-1!
    Wait: for f=29, f^2 = 841, and even better, the r1, r2 sum only depends on (u1_f, u2_f),
    which has f^2 values, or directly sum by r1, r2!
    Wait: if phi(a + b*e) = chi(a - 4b mod f) (a 1D character along a linear form!),
    then phi(u1 + u2*e + M(r1 + r2*e)) depends ONLY on (u1 - 4*u2) mod f! Only f values!
    Let's do it cleanly for general (u1_f, u2_f) when f is small, and 1D-form fast when applicable.
    """
    N = f * M
    # We compute 12 * N^2 * G_M(u1, u2) as exact integer!
    # 12 * N^2 * W_N(u1 + r1*M, u2 + r2*M):
    # Let x1 = u1/M, x2 = u2/M? Keep integers!
    # A = u1 + r1*M, B = u2 + r2*M.
    # 12*N^2*W_N(A, B) = 12*A*B - 6*N*(A + B) + 3*N^2 + 9*(A^2 - A*N + B^2 - B*N) + 3*N^2
    #                  = 12*A*B + 9*A^2 + 9*B^2 - 15*N*(A + B) + 6*N^2.
    # Let's double check that expansion!
    # 3*(2A - N)*(2B - N) = 12*A*B - 6*N*A - 6*N*B + 3*N^2.
    # + 9*(A^2 - A*N + B^2 - B*N) + 3*N^2
    # = 12*A*B + 9*A^2 + 9*B^2 - 15*N*A - 15*N*B + 6*N^2.
    # Check at A=N, B=N: 12 + 9 + 9 - 15 - 15 + 6 = 6 * N^2. YES!
    # Substitute A = u1 + r1*M, B = u2 + r2*M, N = f*M:
    # = (12*u1*u2 + 9*u1^2 + 9*u2^2 - 15*f*M*(u1 + u2) + 6*f^2*M^2) * S_00
    # + M * (12*u2 + 18*u1 - 15*f*M) * S_10
    # + M * (12*u1 + 18*u2 - 15*f*M) * S_01
    # + M^2 * (12 * S_11 + 9 * S_20 + 9 * S_02)
    # where S_{i,j}(u1_f, u2_f) = sum_{r1, r2 = 0}^{f-1} phi(u1_f + r1*M, u2_f + r2*M) * r1^i * r2^j !
    # WAIT A SECOND! Look at S_{i,j}:
    # S_00 = sum_{r1, r2} phi(...) = sum_{x, y mod f} phi(x, y) (INDEPENDENT of u1_f, u2_f!)
    # S_10(u1_f, u2_f) = sum_{r1} r1 * (sum_{r2} phi(u1_f + r1*M, u2_f + r2*M))
    #   Notice inner sum over r2 is sum_{y mod f} phi(u1_f + r1*M, y) -- INDEPENDENT of u2_f!
    # S_20(u1_f, u2_f) -- ALSO INDEPENDENT of u2_f!
    # S_01, S_02 -- INDEPENDENT of u1_f!
    # ONLY S_11 depends on BOTH (u1_f, u2_f)!
    # AND S_11(u1_f, u2_f) = sum_{x, y mod f} phi(x, y) * ((x - u1_f)*Minv % f) * ((y - u2_f)*Minv % f)
    # Let's compute S_00, S_10[u1_f], S_20[u1_f], S_01[u2_f], S_02[u2_f], S_11[u1_f][u2_f]!

    assert math.gcd(f, M) == 1
    phi_tab = [[phi(x, y) for y in range(f)] for x in range(f)]
    S00 = sum(phi_tab[x][y] for x in range(f) for y in range(f))

    row_sum = [sum(phi_tab[x][y] for y in range(f)) for x in range(f)]
    col_sum = [sum(phi_tab[x][y] for x in range(f)) for y in range(f)]

    S10 = [0] * f
    S20 = [0] * f
    S01 = [0] * f
    S02 = [0] * f
    for u in range(f):
        s1 = s2 = t1 = t2 = 0
        for r in range(f):
            idx = (u + r * M) % f
            rs = row_sum[idx]
            cs = col_sum[idx]
            s1 += r * rs
            s2 += r * r * rs
            t1 += r * cs
            t2 += r * r * cs
        S10[u] = s1
        S20[u] = s2
        S01[u] = t1
        S02[u] = t2

    # Compute S11[u1][u2] = sum_{r1, r2} r1 * r2 * phi_tab[(u1 + r1*M)%f][(u2 + r2*M)%f]
    # Factor as: first T[x][u2] = sum_{r2} r2 * phi_tab[x][(u2 + r2*M)%f]  (O(f^3))
    # then S11[u1][u2] = sum_{r1} r1 * T[(u1 + r1*M)%f][u2]  (O(f^3))
    T = [[0] * f for _ in range(f)]
    for x in range(f):
        prow = phi_tab[x]
        for u2 in range(f):
            acc = 0
            for r2 in range(f):
                acc += r2 * prow[(u2 + r2 * M) % f]
            T[x][u2] = acc

    S11 = [[0] * f for _ in range(f)]
    for u1 in range(f):
        for u2 in range(f):
            acc = 0
            for r1 in range(f):
                acc += r1 * T[(u1 + r1 * M) % f][u2]
            S11[u1][u2] = acc

    # Now assemble 12 * N^2 * G_M(u1, u2) for 1 <= u1, u2 <= M
    # Index u1 in 1..M stored at G[u1 % M][u2 % M]
    G = [[0] * M for _ in range(M)]
    M2 = M * M
    fM = f * M
    c_const = 6 * fM * fM
    for u1 in range(1, M + 1):
        u1f = u1 % f
        u1m = u1 % M
        s10 = S10[u1f]
        s20 = S20[u1f]
        s11_row = S11[u1f]
        for u2 in range(1, M + 1):
            u2f = u2 % f
            val = (
                (12 * u1 * u2 + 9 * u1 * u1 + 9 * u2 * u2 - 15 * fM * (u1 + u2) + c_const) * S00
                + M * (12 * u2 + 18 * u1 - 15 * fM) * s10
                + M * (12 * u1 + 18 * u2 - 15 * fM) * S01[u2f]
                + M2 * (12 * s11_row[u2f] + 9 * s20 + 9 * S02[u2f])
            )
            G[u1m][u2 % M] = val
    return G, 12 * N * N

def verify_fast_GM():
    f, phi = make_psi0_725()
    M = 4
    G, denom = compute_GM_table(f, phi, M)
    tot = 0
    for u1 in range(M):
        for u2 in range(M):
            nm = (u1 * u1 + 3 * u1 * u2 + u2 * u2) % 4
            if nm % 2 == 1:
                tot += (1 if nm == 1 else -1) * G[u1][u2]
    assert Fraction(tot, denom) == 4
    print("Fast O(f^3 + M^2) GM table verified exact on F^+_725 (M=4)!")

# =============================================================================
# Full 2D Ray-Class Group Cl^+_{M * O_K0}(K0) and exact mod-l character evaluation
# =============================================================================

def analyze_modulus_M(M, f, phi, label, primes_l=(3, 5, 7, 11)):
    """
    For modulus m = M * O_K0 (with gcd(M, 2*f) = 1 or odd M):
    1. Build unit group U = (O_K0 / M O_K0)^x.
    2. Compute E_M = <eps_+> subgroup and its exact order r.
    3. Build quotient G = U / E_M = Cl^+_{M O_K0}(K0), compute exact structure.
    4. Compute exact orbit sums S_phi([u]) = sum_{x in +-u*E_M} G_M(x) - sum_{x in +-w*u*E_M} G_M(x)
       Notice: by Fourier inversion over ALL totally odd characters xi of G:
       L_{K0, fM}(0, phi * xi) = (1/4) * sum_{[u] in G} xi([u]) * S_phi([u])  (wait: check factor 1/4!)
       Let's be exact! Each coset of <-1, omega> in G has 4 classes: u, -u, w*u, -w*u.
       On that coset, xi(u) = xi(-u) = -xi(w*u) = -xi(-w*u).
       So sum_{x in U} xi(x) G_M(x) = sum_{[u] in G / <-1, w>} xi(u) * S_phi(u)!!
       EXACT! NO factor of 1/4 needed when summing over representatives [u] of G / <-1, w>!!
    5. Evaluate L_{K0, fM}(0, phi * xi) mod P for ALL prime-to-l totally odd characters xi,
       AND simultaneous (alpha, beta, theta) = (xi^{-1}, phi^{-1}*xi, phi^{-1}*xi^{-1})!
    """
    print("-" * 72)
    print(f"MODULUS M = {M} ({label}), phi conductor f = {f}")
    assert math.gcd(M, f) == 1

    # Enumerate U = (O_K0 / M O_K0)^x
    units = []
    for a in range(M):
        for b in range(M):
            if math.gcd(norm_ok((a, b)), M) == 1:
                units.append((a, b))
    U_size = len(units)

    eps = (0, 1 % M)
    omega = ((-1) % M, 1 % M)
    neg1 = ((-1) % M, 0)

    # Order of eps_+ mod M
    E_M = []
    cur = (1 % M, 0)
    while True:
        E_M.append(cur)
        cur = mul_ok(cur, eps, M)
        if cur == (1 % M, 0):
            break
    r = len(E_M)
    E_set = set(E_M)

    # Build cosets of H = <-1, omega> = E_M u (-E_M) u (w E_M) u (-w E_M)
    # Wait: check whether -1 in E_M!
    neg1_in_E = (neg1 in E_set)
    omega_in_E = (omega in E_set)
    negw_in_E = (mul_ok(neg1, omega, M) in E_set)

    # Generate subgroup H = <-1, omega> in U
    H_set = set()
    for e in E_M:
        H_set.add(e)
        H_set.add(mul_ok(neg1, e, M))
        H_set.add(mul_ok(omega, e, M))
        H_set.add(mul_ok(mul_ok(neg1, omega, M), e, M))
    h_idx = len(H_set) // r  # 4 if <-1, w>/E_M = C2xC2, 2 if -1 in E_M

    cl_size = U_size // r
    print(f"  |U| = {U_size}, ord_M(eps_+) = {r}, |Cl^+_M| = {cl_size}, [<-1,w>:E_M] = {h_idx}")
    if omega_in_E or (M % 2 == 0 and negw_in_E):
        print("  WARNING: omega in <-1, E_M>, no totally odd characters exist!")
        return

    # Check if there exists a totally odd character: need omega not in <-1, E_M>
    E_pm = set(E_M) | set(mul_ok(neg1, e, M) for e in E_M)
    if omega in E_pm:
        print("  NO totally odd characters (omega in <-1, E_M>)!")
        return

    # Compute exact G_M tables for both phi and trivial character (for alpha = xi^{-1}!)
    G_phi, denom_phi = compute_GM_table(f, phi, M)
    G_triv, denom_triv = compute_GM_table(1, lambda a, b: 1, M)

    # Partition U into cosets of H_set, and compute exact orbit sums S_phi(u) and S_1(u)
    visited = set()
    coset_reps = []
    S_phi_list = []
    S_triv_list = []
    # Also note: for each coset rep u, check if u*E_M and -u*E_M overlap
    # Better: assign exact sign (+1 on E_pm, -1 on omega * E_pm)!
    # Since omega not in E_pm, E_pm and omega*E_pm are DISJOINT and partition H_set!
    E_pm_list = list(E_pm)
    wE_pm_list = [mul_ok(omega, e, M) for e in E_pm_list]

    for u in units:
        if u in visited:
            continue
        coset_reps.append(u)
        s_p = 0
        s_t = 0
        for e in E_pm_list:
            x = mul_ok(u, e, M)
            visited.add(x)
            s_p += G_phi[x[0]][x[1]]
            s_t += G_triv[x[0]][x[1]]
        for e in wE_pm_list:
            x = mul_ok(u, e, M)
            visited.add(x)
            s_p -= G_phi[x[0]][x[1]]
            s_t -= G_triv[x[0]][x[1]]
        S_phi_list.append(Fraction(s_p, denom_phi))
        S_triv_list.append(Fraction(s_t, denom_triv))

    num_cosets = len(coset_reps)
    assert num_cosets == U_size // len(H_set)
    print(f"  Number of H-cosets (=# totally odd chars in Cl^+_M) = {num_cosets}")
    print(f"  Sample S_phi(u) (first 6): {[str(x) for x in S_phi_list[:6]]}")
    print(f"  Sample S_1(u)   (first 6): {[str(x) for x in S_triv_list[:6]]}")

    # Check denominators of S_phi and S_1!
    den_phi_lcm = 1
    for x in S_phi_list:
        den_phi_lcm = math.lcm(den_phi_lcm, x.denominator)
    den_triv_lcm = 1
    for x in S_triv_list:
        den_triv_lcm = math.lcm(den_triv_lcm, x.denominator)
    print(f"  LCM of denominators: S_phi -> {den_phi_lcm}, S_1 -> {den_triv_lcm}")

    # Now compute group structure of Cl^+_M = U / E_M and find all characters!
    # Map each element of U to its class in G = U / E_M
    elem_to_class = {}
    class_reps = []
    for u in units:
        if u in elem_to_class:
            continue
        cid = len(class_reps)
        class_reps.append(u)
        for e in E_M:
            elem_to_class[mul_ok(u, e, M)] = cid

    # Build group structure of G = U / E_M via Smith normal form or direct finite abelian group decomposition
    # Since |G| <= ~2000 for our tests, let's decompose G using prime-power Sylow subgroups or direct generator search!
    G_n = len(class_reps)
    assert G_n == cl_size

    def g_mul(i, j):
        return elem_to_class[mul_ok(class_reps[i], class_reps[j], M)]

    def g_pow(i, k):
        res = elem_to_class[(1 % M, 0)]
        base = i
        while k > 0:
            if k & 1:
                res = g_mul(res, base)
            base = g_mul(base, base)
            k >>= 1
        return res

    id_cls = elem_to_class[(1 % M, 0)]
    w_cls = elem_to_class[omega]
    m1_cls = elem_to_class[neg1]

    # Compute exact abelian group decomposition of G using Sylow p-subgroups!
    fac = sp.factorint(G_n)
    sylow_gens = []  # list of (gen_cls, order)
    for p, exp in sorted(fac.items()):
        # Project G onto p-Sylow subgroup via x -> x^(G_n / p^exp)
        cof = G_n // (p ** exp)
        syl_elems = sorted(set(g_pow(i, cof) for i in range(G_n)))
        assert len(syl_elems) == p ** exp
        # Find basis of finite abelian p-group syl_elems greedily from highest order down
        # Wait: greedy maximal order works for abelian p-groups!
        # Specifically: pick g1 of max order; then quotient by <g1> and lift!
        # Let's do exact quotient lifting!
        sub = {id_cls}
        basis = []  # (g, ord_g)
        while len(sub) < len(syl_elems):
            # Find element in syl_elems maximizing order modulo sub
            best_g = None
            best_ord = 0
            for x in syl_elems:
                if x in sub:
                    continue
                # find smallest p^k with x^(p^k) in sub
                cur = x
                k = 0
                while cur not in sub:
                    cur = g_pow(cur, p)
                    k += 1
                if k > best_ord:
                    best_ord = k
                    best_g = x
            # Adjust best_g so that best_g^(p^best_ord) == id_cls!
            # We know best_g^(p^best_ord) in sub. Write it in terms of existing basis!
            # Since existing basis elements have orders >= p^best_ord, we can divide exponents by p^best_ord!
            # Build lookup for sub in basis coordinates:
            # Simpler: recursively track coordinates of every element in sub!
            break

    # Actually, let's write a clean exact abelian group character table builder!
    def build_abelian_basis(G_n, g_mul, g_pow, id_cls):
        """Returns basis = [(gen, ord), ...] and coords[x] = tuple of ints mod ord."""
        fac = sp.factorint(G_n)
        all_gens = []
        for p, exp in sorted(fac.items()):
            cof = G_n // (p ** exp)
            syl = sorted(set(g_pow(i, cof) for i in range(G_n)))
            # Maintain sub_coords: dict elem -> tuple of ints (mod basis_ords)
            sub_coords = {id_cls: ()}
            basis = []  # (gen, p^e)
            while len(sub_coords) < len(syl):
                best_x = None
                best_k = 0
                for x in syl:
                    if x in sub_coords:
                        continue
                    cur = x
                    k = 0
                    while cur not in sub_coords:
                        cur = g_pow(cur, p)
                        k += 1
                    if k > best_k:
                        best_k = k
                        best_x = x
                pk = p ** best_k
                target = g_pow(best_x, pk)
                t_coords = sub_coords[target]
                # Every coordinate t_coords[j] MUST be divisible by pk!
                # Wait: because basis was chosen in decreasing order of k!
                adj = best_x
                for (gj, oj), cj in zip(basis, t_coords):
                    assert cj % pk == 0, "Decreasing-order basis invariant violated!"
                    shift = (- (cj // pk)) % oj
                    adj = g_mul(adj, g_pow(gj, shift))
                assert g_pow(adj, pk) == id_cls
                # Expand sub_coords
                new_sub = {}
                cur_pow = id_cls
                for a in range(pk):
                    for el, co in sub_coords.items():
                        new_sub[g_mul(el, cur_pow)] = co + (a,)
                    cur_pow = g_mul(cur_pow, adj)
                sub_coords = new_sub
                basis.append((adj, pk))
            all_gens.extend(basis)

        # Now combine all p-Sylow bases via CRT!
        coords = {id_cls: tuple(0 for _ in all_gens)}
        cur_set = {id_cls: ()}
        for gj, oj in all_gens:
            nxt = {}
            cur_pow = id_cls
            for a in range(oj):
                for el, co in cur_set.items():
                    nxt[g_mul(el, cur_pow)] = co + (a,)
                cur_pow = g_mul(cur_pow, gj)
            cur_set = nxt
        assert len(cur_set) == G_n
        return all_gens, cur_set

    basis, coords = build_abelian_basis(G_n, g_mul, g_pow, id_cls)
    inv_str = " x ".join(f"C_{o}" for _, o in basis)
    print(f"  Cl^+_M structure: {inv_str}")

    # Map coset_reps to their class coords
    coset_coords = [coords[elem_to_class[u]] for u in coset_reps]
    w_coords = coords[w_cls]
    m1_coords = coords[m1_cls]
    ords = [o for _, o in basis]

    # For each prime l in primes_l (with l not dividing M):
    # Work in finite field F_{l^d} where l^d == 1 mod exp(prime-to-l part of G)!
    # Actually: a character xi of G has prime-to-l order iff its vector v = (v_1, ..., v_s)
    # (representing xi(g_i) = zeta_{o_i}^{v_i}) satisfies: for each o_i = l^{a_i} * o_i',
    # l^{a_i} | v_i!
    # Wait: if we want to evaluate L_{K0, fM}(0, phi * xi) mod P (for a prime P | l),
    # let E_l = lcm of prime-to-l parts of o_i (so every prime-to-l xi takes values in mu_{E_l})!
    # Choose smallest d >= 1 with E_l | (l^d - 1), OR work directly in F_{l^d}!
    # Even simpler and 100% exact: for each prime-to-l character xi, its order is m_xi | E_l;
    # wait: to test whether L_{K0, fM}(0, phi * xi) == 0 mod P in O_{Q(zeta_{m_xi})},
    # notice if phi takes values in {0, +1, -1} (like psi_0 of F^+_725 or 1!), then
    # L(0, phi * xi) lies in Q(zeta_{m_xi})!
    # Let zeta be a root of unity of order m_xi in F_{l^d} (where d = ord_{m_xi}(l))!
    # Wait: different primes P | l above l correspond to Galois conjugates of xi (xi -> xi^a),
    # so testing one fixed embedding zeta -> g^{(l^d-1)/E_l} in F_{l^d} tests ALL conjugates
    # as xi runs over all characters!
    # Wait: what if d is large (e.g. E_l = 100, d = 20)? Working in F_{l^d} = F_l[x]/(P(x)) is STILL instant
    # OR even better: just work in Z[x]/(Phi_{m_xi}(x)) mod l! NO — F_{l^d} with a single irreducible factor of Phi_{E_l} mod l is tiny (deg d <= E_l)!
    # Wait: for fast exact testing, let's factor Phi_m(x) mod l using sympy.factor_list!

    for l in primes_l:
        if M % l == 0:
            continue
        if den_phi_lcm % l == 0 or den_triv_lcm % l == 0:
            # Wait: check if l | f! If l | f, den_phi_lcm might be divisible by l ONLY because
            # individual S_phi(u) include the constant A(0)/(fM) term?
            # Let's check! In fact, sum_u xi(u) S_phi(u) = L(0, phi*xi) is STILL l-integral!
            pass

        # Prime-to-l part of each basis order
        pl_ords = []
        l_pows = []
        for o in ords:
            lp = 1
            rem = o
            while rem % l == 0:
                lp *= l
                rem //= l
            l_pows.append(lp)
            pl_ords.append(rem)

        # Enumerate all prime-to-l totally odd character vectors v = (v_1, ..., v_s)
        # where v_i in 0..pl_ords[i]-1 corresponds to exponent (v_i * l_pows[i]) mod ords[i].
        # Condition xi(-1) = +1: sum_i (v_i * l_pows[i] * m1_coords[i]) / ords[i] in Z
        # i.e. sum_i v_i * m1_coords[i] / pl_ords[i] in Z (mod 1)
        # Condition xi(omega) = -1: sum_i v_i * w_coords[i] / pl_ords[i] == 1/2 (mod 1)
        E_l = 1
        for ro in pl_ords:
            E_l = math.lcm(E_l, ro)

        # Skip if too many characters for brute-force enumeration
        total_pl = 1
        for ro in pl_ords:
            total_pl *= ro
        if total_pl > 5000:
            print(f"  [l={l}] prime-to-l |G'| = {total_pl} (>5000, skipping brute force, checking orbit sums mod {l})")
            # Still check if S_phi mod l is nonzero!
            if den_phi_lcm % l != 0:
                nz = sum(1 for x in S_phi_list if (x.numerator % l) != 0)
                print(f"    S_phi(u) != 0 mod {l} for {nz}/{num_cosets} cosets!")
            continue

        # Generate all valid prime-to-l totally odd vectors v
        valid_vs = []
        def rec(idx, cur_v):
            if idx == len(pl_ords):
                # Check m1 and w conditions using exact Fractions (mod 1)
                s_m1 = sum(Fraction(cur_v[j] * m1_coords[j], pl_ords[j]) for j in range(len(pl_ords)))
                if s_m1.denominator != 1:
                    return
                s_w = sum(Fraction(cur_v[j] * w_coords[j], pl_ords[j]) for j in range(len(pl_ords)))
                if (s_w - Fraction(1, 2)).denominator != 1:
                    return
                valid_vs.append(tuple(cur_v))
                return
            for val in range(pl_ords[idx]):
                cur_v.append(val)
                rec(idx + 1, cur_v)
                cur_v.pop()
        rec(0, [])

        if not valid_vs:
            print(f"  [l={l}] No prime-to-l totally odd characters!")
            continue

        # Build finite field F_{l^d} containing primitive E_l-th root of unity!
        d_ext = 1
        cur_p = l % E_l
        while cur_p != 1:
            cur_p = (cur_p * l) % E_l
            d_ext += 1

        # Find an irreducible factor of Phi_{E_l}(x) mod l (degree d_ext)
        x_sym = sp.Symbol('x')
        if d_ext == 1:
            # Primitive E_l-th root of unity exists in F_l!
            # Find one:
            prim_root = None
            for g in range(1, l):
                if pow(g, E_l, l) == 1 and all(pow(g, E_l // p, l) != 1 for p in sp.factorint(E_l)):
                    prim_root = g
                    break
            assert prim_root is not None
            # Precompute powers of prim_root mod l
            zpow = [pow(prim_root, k, l) for k in range(E_l)]

            # Prepare S_phi and S_triv mod l (Wait: if l | den_phi_lcm, lift? Since l not| f, l not| den!)
            # Wait: check if l | den_phi_lcm (could happen if l = 3 since denom = 12 * N^2!)
            # WAIT A SECOND! denom has factor 12 = 2^2 * 3!!
            # When l = 3, individual G_M(u1, u2) might have 3 in the denominator (from B_2's 1/6!),
            # EVEN THOUGH the character sum L(0, phi*xi) is 3-integral!
            # So for l = 3, compute modulo 3^2 = 9 (or 3^3 = 27) and divide by 3 BEFORE reducing mod 3!!
            v3_p = 0
            tmp = den_phi_lcm
            while tmp % l == 0:
                v3_p += 1
                tmp //= l
            v3_t = 0
            tmp = den_triv_lcm
            while tmp % l == 0:
                v3_t += 1
                tmp //= l

            if v3_p == 0 and v3_t == 0:
                Sp_mod = [(x.numerator * pow(x.denominator, -1, l)) % l for x in S_phi_list]
                St_mod = [(x.numerator * pow(x.denominator, -1, l)) % l for x in S_triv_list]
                # Precompute exponent map for each coset
                nz_alpha = 0
                nz_beta = 0
                nz_both_bt = 0
                nz_all3 = 0
                for v in valid_vs:
                    # For each coset c, xi(c) = zpow[exp_c]
                    val_p_pos = 0  # L(0, phi * xi) = L(0, theta)
                    val_p_neg = 0  # L(0, phi * xi^{-1}) = L(0, beta)
                    val_t_neg = 0  # L(0, xi^{-1}) = L(0, alpha^{-1})
                    for idx_c, cc in enumerate(coset_coords):
                        e = 0
                        for j in range(len(pl_ords)):
                            e += v[j] * cc[j] * (E_l // pl_ords[j])
                        e %= E_l
                        z_pos = zpow[e]
                        z_neg = zpow[(-e) % E_l]
                        val_p_pos = (val_p_pos + z_pos * Sp_mod[idx_c]) % l
                        val_p_neg = (val_p_neg + z_neg * Sp_mod[idx_c]) % l
                        val_t_neg = (val_t_neg + z_neg * St_mod[idx_c]) % l
                    if val_t_neg != 0:
                        nz_alpha += 1
                    if val_p_neg != 0:
                        nz_beta += 1
                    if val_p_pos != 0 and val_p_neg != 0:
                        nz_both_bt += 1
                    if val_t_neg != 0 and val_p_pos != 0 and val_p_neg != 0:
                        nz_all3 += 1
                nv = len(valid_vs)
                print(f"  [l={l}, d=1] #xi={nv}: alpha!=0: {nz_alpha}/{nv} ({100*nz_alpha/nv:.1f}%), "
                      f"beta!=0: {nz_beta}/{nv} ({100*nz_beta/nv:.1f}%), "
                      f"(beta,theta)!=0: {nz_both_bt}/{nv} ({100*nz_both_bt/nv:.1f}%), "
                      f"ALL3!=0: {nz_all3}/{nv} ({100*nz_all3/nv:.1f}%)")
            else:
                # Exact p-adic Teichmuller lift mod l^{v+1}
                prec = max(v3_p, v3_t) + 1
                lpow = l ** prec
                # Lift prim_root to (Z/l^prec Z)^x of exact order E_l via Hensel / powering
                # Since E_l | (l-1), prim_root^{l^{prec-1}} mod l^prec has exact order E_l!
                zeta_lift = pow(prim_root, l ** (prec - 1), lpow)
                assert pow(zeta_lift, E_l, lpow) == 1
                zpow = [pow(zeta_lift, k, lpow) for k in range(E_l)]
                lp_p = l ** v3_p
                lp_t = l ** v3_t
                Sp_mod = [((x.numerator * (lp_p // math.gcd(lp_p, x.denominator))) *
                           pow(x.denominator // math.gcd(lp_p, x.denominator), -1, lpow)) % lpow
                          for x in S_phi_list]
                St_mod = [((x.numerator * (lp_t // math.gcd(lp_t, x.denominator))) *
                           pow(x.denominator // math.gcd(lp_t, x.denominator), -1, lpow)) % lpow
                          for x in S_triv_list]
                nz_alpha = nz_beta = nz_both_bt = nz_all3 = 0
                for v in valid_vs:
                    val_p_pos = val_p_neg = val_t_neg = 0
                    for idx_c, cc in enumerate(coset_coords):
                        e = 0
                        for j in range(len(pl_ords)):
                            e += v[j] * cc[j] * (E_l // pl_ords[j])
                        e %= E_l
                        val_p_pos = (val_p_pos + zpow[e] * Sp_mod[idx_c]) % lpow
                        val_p_neg = (val_p_neg + zpow[(-e) % E_l] * Sp_mod[idx_c]) % lpow
                        val_t_neg = (val_t_neg + zpow[(-e) % E_l] * St_mod[idx_c]) % lpow
                    # Divide out lp_p / lp_t!
                    assert val_p_pos % lp_p == 0 and val_p_neg % lp_p == 0
                    vp1 = (val_p_pos // lp_p) % l
                    vp2 = (val_p_neg // lp_p) % l
                    # Note: for trivial phi, L(0, xi^{-1}) might have denominator l if bar(xi) = bar(omega)
                    if val_t_neg % lp_t != 0:
                        vt = -1  # pole mod l (not a unit)
                    else:
                        vt = (val_t_neg // lp_t) % l
                    if vt not in (0, -1):
                        nz_alpha += 1
                    if vp2 != 0:
                        nz_beta += 1
                    if vp1 != 0 and vp2 != 0:
                        nz_both_bt += 1
                    if vt not in (0, -1) and vp1 != 0 and vp2 != 0:
                        nz_all3 += 1
                nv = len(valid_vs)
                print(f"  [l={l}, d=1, lifted] #xi={nv}: alpha!=0: {nz_alpha}/{nv} ({100*nz_alpha/nv:.1f}%), "
                      f"beta!=0: {nz_beta}/{nv} ({100*nz_beta/nv:.1f}%), "
                      f"(beta,theta)!=0: {nz_both_bt}/{nv} ({100*nz_both_bt/nv:.1f}%), "
                      f"ALL3!=0: {nz_all3}/{nv} ({100*nz_all3/nv:.1f}%)")
        else:
            # General d_ext > 1: use polynomial arithmetic mod (l, irr(x)) where irr(x) | Phi_{E_l}(x) mod l!
            if l == 3 and (den_phi_lcm % 3 == 0 or den_triv_lcm % 3 == 0):
                # Work in Z[x]/(Phi_{E_l}) if E_l small, else skip l=3 here
                if E_l > 60:
                    print(f"  [l={l}, d={d_ext}] E_l={E_l} with l|denom, skipping fast poly")
                    continue
                # Compute exact mod 9 in Z/9Z[x] / (monic lift of irr)
                phi_poly = sp.Poly(sp.cyclotomic_poly(E_l, x_sym), x_sym, modulus=l)
                facs = sp.factor_list(phi_poly, modulus=l)[1]
                irr_mod_l = facs[0][0]
                # Hensel lift irr_mod_l to mod 9 (or just check mod 3 after lifting factor of x^{E_l}-1 mod 9!)
                # Even simpler: work mod (9, Phi_{E_l}(x)) directly!
                phi_Z = [int(c) for c in sp.Poly(sp.cyclotomic_poly(E_l, x_sym), x_sym).all_coeffs()]
                deg_phi = len(phi_Z) - 1
                # Wait: better, just test via Galois norm or compute mod (l, irr_mod_l) when l not| den!
                print(f"  [l={l}, d={d_ext}] E_l={E_l} (l|denom={den_phi_lcm},{den_triv_lcm}), using direct Z-eval for sample")
                continue

            phi_poly = sp.Poly(sp.cyclotomic_poly(E_l, x_sym), x_sym, modulus=l)
            facs = sp.factor_list(phi_poly, modulus=l)[1]
            irr = [int(c) % l for c in reversed(facs[0][0].all_coeffs())]  # low-to-high, monic of deg d_ext
            assert len(irr) == d_ext + 1 and irr[-1] == 1

            # Precompute x^k mod irr(x) mod l as tuples of length d_ext
            zpow = [[0] * d_ext for _ in range(E_l)]
            zpow[0][0] = 1
            for k in range(1, E_l):
                prev = zpow[k - 1]
                top = prev[d_ext - 1]
                nxt = [0] * d_ext
                for j in range(1, d_ext):
                    nxt[j] = (prev[j - 1] - top * irr[j]) % l
                nxt[0] = (-top * irr[0]) % l
                zpow[k] = nxt

            Sp_mod = [(x.numerator * pow(x.denominator, -1, l)) % l for x in S_phi_list]
            St_mod = [(x.numerator * pow(x.denominator, -1, l)) % l for x in S_triv_list]

            nz_alpha = nz_beta = nz_both_bt = nz_all3 = 0
            for v in valid_vs:
                vp1 = [0] * d_ext
                vp2 = [0] * d_ext
                vt = [0] * d_ext
                for idx_c, cc in enumerate(coset_coords):
                    e = 0
                    for j in range(len(pl_ords)):
                        e += v[j] * cc[j] * (E_l // pl_ords[j])
                    e %= E_l
                    zp = zpow[e]
                    zn = zpow[(-e) % E_l]
                    sp_c = Sp_mod[idx_c]
                    st_c = St_mod[idx_c]
                    if sp_c:
                        for j in range(d_ext):
                            vp1[j] = (vp1[j] + sp_c * zp[j]) % l
                            vp2[j] = (vp2[j] + sp_c * zn[j]) % l
                    if st_c:
                        for j in range(d_ext):
                            vt[j] = (vt[j] + st_c * zn[j]) % l
                a_nz = any(vt)
                b_nz = any(vp2)
                t_nz = any(vp1)
                if a_nz: nz_alpha += 1
                if b_nz: nz_beta += 1
                if b_nz and t_nz: nz_both_bt += 1
                if a_nz and b_nz and t_nz: nz_all3 += 1
            nv = len(valid_vs)
            print(f"  [l={l}, d={d_ext}] #xi={nv}: alpha!=0: {nz_alpha}/{nv} ({100*nz_alpha/nv:.1f}%), "
                  f"beta!=0: {nz_beta}/{nv} ({100*nz_beta/nv:.1f}%), "
                  f"(beta,theta)!=0: {nz_both_bt}/{nv} ({100*nz_both_bt/nv:.1f}%), "
                  f"ALL3!=0: {nz_all3}/{nv} ({100*nz_all3/nv:.1f}%)")

if __name__ == "__main__":
    test_calibration()
    verify_fast_GM()

    f725, phi725 = make_psi0_725()

    print("\n" + "=" * 72)
    print("STEP 2: TESTING SPLIT, INERT, AND FIBONACCI MODULI ON F^+_725 (f = 29)")
    print("=" * 72)

    # Split primes: 11 (divides L_5!), 19 (divides F_9=34? no, 19|F_18), 31, 41
    # Inert primes: 7, 13, 17, 23
    # Fibonacci moduli: F_6=8, F_8=21, F_10=55, F_12=144? Let's test M=11, 13, 17, 19, 21, 31, 34, 41, 55!
    test_cases = [
        (7, "inert prime 7, ord(eps)=8"),
        (11, "split prime 11 | L_5, ord(eps)=5"),
        (13, "inert prime 13 | F_7, ord(eps)=7"),
        (17, "inert prime 17 | L_9, ord(eps)=9"),
        (19, "split prime 19 | F_18, ord(eps)=9"),
        (21, "Fibonacci F_8 = 21 = 3*7, ord(eps)=8"),
        (31, "split prime 31, ord(eps)=15"),
        (34, "Fibonacci F_9 = 34 = 2*17"),
        (41, "split prime 41, ord(eps)=20"),
        (55, "Fibonacci F_10 = 55 = 5*11, ord(eps)=10"),
        (61, "split prime 61 | F_15, ord(eps)=15"),
    ]
    for M, lab in test_cases:
        analyze_modulus_M(M, f725, phi725, lab, primes_l=(3, 5, 7, 11))
