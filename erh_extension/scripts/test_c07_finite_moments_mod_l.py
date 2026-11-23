#!/usr/bin/env python3
"""
Wave-5 C07 Exploration Script:
Path 4 (Finite Character Moments mod l over Q and K_0 = Q(sqrt(5)))
AND exact structure of C(a) = (1/|X|) sum_{chi in X} chi(a) L(0, psi_1 chi) L(0, psi_2 chi^{-1})
and triple moments S_3(a)!
"""

import math
from fractions import Fraction
import sympy as sp

def kronecker(a, n):
    if n == 0:
        return 1 if abs(a) == 1 else 0
    if n == 1:
        return 1
    if n < 0:
        return (-1 if a < 0 else 1) * kronecker(a, -n)
    res = 1
    v2 = 0
    while (n & 1) == 0:
        n >>= 1
        v2 += 1
    if v2:
        if (a & 1) == 0:
            return 0
        if v2 & 1 and (a & 7) in (3, 5):
            res = -res
    if n > 1:
        if math.gcd(a, n) > 1:
            return 0
        res *= int(sp.jacobi_symbol(a % n, n))
    return res

# =============================================================================
# PART 1: EXACT FINITE MOMENTS OVER Q
# =============================================================================
def g_Q(phi_fn, f, q):
    """
    For even character phi_fn mod f (f=1 means trivial), gcd(f, q) = 1:
    Returns list g[u] for u = 0..q-1 such that for any odd chi mod q (even imprimitive if chi(-1)=-1):
      L(0, phi * chi) = -B_{1, phi*chi} = sum_{u=1}^{q-1} chi(u) g[u]
    Specifically g[u] = -(1/(f*q)) sum_{r=0}^{f-1} phi(u + r*q) * (u + r*q) + (1/2 if f==1 else 0)...
    Wait: for ANY odd chi mod q, sum_{u=1}^{q-1} chi(u) = 0, so adding any constant doesn't change sum.
    To make g[q - u] = -g[u] explicitly:
      g[u] = -sum_{r=0}^{f-1} phi(u + r*q) * ((u + r*q)/(f*q) - 1/2)
    Check: for f=1, g[u] = 1/2 - u/q, so g[q-u] = -g[u].
    For f>1 nontrivial even, sum_r phi(u+rq) = 0, so g[u] = -(1/f) sum_{r=0}^{f-1} r * phi(u + r*q)
    WAIT: check if -(1/f) sum_{r=0}^{f-1} r * phi(u + r*q) satisfies g[q-u] = -g[u]!
    At q - u: sum_{r=0}^{f-1} r * phi(q - u + r*q) = sum_{r=0}^{f-1} r * phi(-u + (r+1)*q)
      = sum_{r=0}^{f-1} r * phi(u - (r+1)*q). Let r' = f - 1 - r (runs 0..f-1):
      (r+1) = f - r' => phi(u + r'*q) * (f - 1 - r').
      Sum = (f-1)*sum phi - sum r' phi = -sum r' phi! YES, EXACTLY -g[u]!!
    """
    g = [Fraction(0)] * q
    if f == 1:
        for u in range(1, q):
            if math.gcd(u, q) == 1:
                g[u] = Fraction(1, 2) - Fraction(u, q)
    else:
        for u in range(1, q):
            if math.gcd(u, q) == 1:
                s = sum(r * phi_fn((u + r * q) % f) for r in range(f))
                g[u] = Fraction(-s, f)
    # Verify antisymmetry
    for u in range(1, q):
        if math.gcd(u, q) == 1:
            assert g[u] == -g[q - u], f"Antisymmetry failed at u={u}"
    return g

def L_neg1_Q(phi_fn, f):
    """Exact L(-1, phi) = -B_{2, phi} / 2 for even phi mod f."""
    if f == 1:
        return Fraction(-1, 12)
    s = sum(phi_fn(a) * (Fraction(a, f)**2 - Fraction(a, f) + Fraction(1, 6)) for a in range(1, f))
    B2 = f * s
    return -B2 / 2

def test_Q_moments():
    print("=" * 78)
    print("PART 1: EXACT FINITE SECOND & THIRD MOMENTS OVER Q")
    print("=" * 78)

    # Test 1A: psi_1 = 1, psi_2 = chi_5 (even, f=5); L(-1, chi_5) = -B_{2, chi_5}/2 = -2/5
    phi5 = lambda a: kronecker(5, a)
    phi8 = lambda a: kronecker(8, a)
    phi12 = lambda a: kronecker(12, a)
    print(f"L(-1, 1) = {L_neg1_Q(lambda a: 1, 1)}")
    print(f"L(-1, chi_5) = {L_neg1_Q(phi5, 5)}")
    print(f"L(-1, chi_8) = {L_neg1_Q(phi8, 8)}")
    print(f"L(-1, chi_12) = {L_neg1_Q(phi12, 12)}")

    # Formula check:
    # C(a) = (1/|X|) sum_{chi mod q odd} chi(a) L(0, psi_1 chi) L(0, psi_2 chi^{-1})
    #      = 2 * sum_{u in (Z/qZ)^*, 1<=u<q} g1[u] * g2[(a*u) % q]  (Wait: factor 2 because u and -u both give +g1[u]g2[au],
    #        let's verify directly by summing over actual characters for small q!)
    for q in [7, 11, 13, 17, 19, 23, 29, 31]:
        g1 = g_Q(lambda a: 1, 1, q)
        g5 = g_Q(phi5, 5, q)
        # C(a) = 2 * sum_{u=1}^{q-1} g1[u] * g5[(a*u)%q] ? Let's check normalization!
        # L(0, chi) = sum_{u=1}^{q-1} chi(u) g1[u].
        # (1/|X|) sum_{chi odd} chi(a u v^{-1}) = delta_{v=au} - delta_{v=-au}.
        # Sum_{u, v} g1[u] g2[v] (delta_{v=au} - delta_{v=-au})
        #   = sum_u g1[u] (g2[au] - g2[-au]) = 2 * sum_{u=1}^{q-1} g1[u] g2[au].
        # Wait: let's verify at q=7 with direct character sum!
        C1 = 2 * sum(g1[u] * g5[u] for u in range(1, q))
        Cf = 2 * sum(g1[u] * g5[(5 * u) % q] for u in range(1, q))
        Cinvf = 2 * sum(g1[u] * g5[(pow(5, -1, q) * u) % q] for u in range(1, q))
        # Direct verify for q=7:
        if q == 7:
            # odd chars mod 7: gen=3, order 6, odd powers k=1,3,5
            # sum over k=1,3,5 of chi(1) L(0, chi) L(0, chi_5 chi^{-1}) / 3
            zeta = sp.exp(2 * sp.pi * sp.I / 6)
            dlog = {pow(3, k, 7): k for k in range(6)}
            tot = 0
            for e in [1, 3, 5]:
                L1 = sum(zeta**(e * dlog[u]) * sp.Rational(g1[u].numerator, g1[u].denominator) for u in range(1, 7))
                L2 = sum(zeta**(-e * dlog[u]) * sp.Rational(g5[u].numerator, g5[u].denominator) for u in range(1, 7))
                tot += L1 * L2
            tot = sp.simplify(sp.expand_complex(tot / 3))
            assert tot == sp.Rational(C1.numerator, C1.denominator), f"Mismatch: {tot} vs {C1}"
            print(f"  [Direct char-sum check at q=7 PASSED: C(1) = {C1}]")
        # Look at C(a) / q and C(f) / q!
        # Wait: remember from functional equation:
        #   sum chi(f) L(0, chi) L(0, phi chi^{-1}) ~ c * q * phi(q) * L(-1, phi)!!
        # Let's check BOTH C(1) and C(f) and C(f^{-1})!
        # Wait: tau(phi * chi^{-1}) = phi(q) chi^{-1}(f) tau(phi) tau(chi^{-1}),
        # so chi(f) cancels chi^{-1}(f)!!
        # Wait: L(0, chi) L(0, phi chi^{-1}) has chi^{-1}(f), so we multiply by chi(f)!
        # Let's print C(1), C(5), C(5^{-1})!
        # Also check ratio Cf / (q * phi5(q) * L(-1, chi_5))!
        Lneg1 = L_neg1_Q(phi5, 5)  # -2/5
        ratio_f = Cf / (q * phi5(q) * Lneg1)
        print(f"  q={q:2d} (chi5={phi5(q):+d}): C(1)={str(C1):>12}, C(5)={str(Cf):>12}, C(5^-1)={str(Cinvf):>12} | C(5)/(q*chi5(q)*L(-1,chi5)) = {float(ratio_f):.6f} ({ratio_f})")

    print("\n--- Test 1B: EXACT DIFFERENCE C(f) - c * q * phi(q) * L(-1, phi) for chi_5, chi_8, chi_12 ---")
    # Wait: what is the EXACT constant c? Look at ratio_f above!
    # Also check ALL a in (Z/qZ)^* for q = 2^n (n = 4, 5, 6, 7)!
    print("\n--- Test 1C: 2-power modulus N = 2^n on Q, psi_1 = 1, psi_2 = chi_5 ---")
    for n in [3, 4, 5, 6, 7]:
        N = 1 << n
        g1 = g_Q(lambda a: 1, 1, N)
        g5 = g_Q(phi5, 5, N)
        # Note: sum over ALL odd chars mod 2^n (including imprimitive ones!)
        # For primitive odd chars mod 2^n: subtract the N/2 sum!
        # Wait: for imprimitive odd chi mod N, g1[u] = 1/2 - u/N still computes L^{(2)}(0, chi) = L(0, chi) (since chi(2)=0)!
        # Because for ANY odd chi mod 2^n (primitive or not), conductor is a power of 2 >= 4, so chi(2) = 0!
        # Hence L(0, chi) = -B_{1, chi} (mod 2^n) ALWAYS!
        C_all_1 = 2 * sum(g1[u] * g5[u] for u in range(1, N, 2))
        C_all_5 = 2 * sum(g1[u] * g5[(5 * u) % N] for u in range(1, N, 2))
        C_all_inv5 = 2 * sum(g1[u] * g5[(pow(5, -1, N) * u) % N] for u in range(1, N, 2))
        # Also check psi_1 = chi_5, psi_2 = chi_13 (two nontrivial even chars!)
        phi13 = lambda a: kronecker(13, a)
        g13 = g_Q(phi13, 13, N)
        C_5_13_1 = 2 * sum(g5[u] * g13[u] for u in range(1, N, 2))
        # Check for a = 5 * 13^{-1} and a = 13 * 5^{-1}:
        C_5_13_rat = 2 * sum(g5[u] * g13[(13 * pow(5, -1, N) * u) % N] for u in range(1, N, 2))
        C_5_13_rat2 = 2 * sum(g5[u] * g13[(5 * pow(13, -1, N) * u) % N] for u in range(1, N, 2))
        print(f"  N=2^{n}={N:3d}: (1,chi5): C(1)={str(C_all_1):>10}, C(5)={str(C_all_5):>10}, C(5^-1)={str(C_all_inv5):>10} | (chi5,chi13): C(1)={str(C_5_13_1):>10}, C(13/5)={str(C_5_13_rat):>10}, C(5/13)={str(C_5_13_rat2):>10}")

    print("\n--- Test 1D: EXACT polynomial/linear structure of C(a) for (1, chi_5) and (chi_5, chi_13) at N = 2^n! ---")
    # WAIT A SECOND! Look at the output of Test 1C to see if C(a) is an EXACT closed form in N!
    for f_phi, name, phi_fn in [(5, "chi_5", phi5), (13, "chi_13", lambda a: kronecker(13, a)), (29, "chi_29", lambda a: kronecker(29, a))]:
        print(f"  Host phi = {name} (f={f_phi}, L(-1,phi)={L_neg1_Q(phi_fn, f_phi)}):")
        for n in [4, 5, 6, 7, 8]:
            N = 1 << n
            g1 = g_Q(lambda a: 1, 1, N)
            gp = g_Q(phi_fn, f_phi, N)
            C_f = 2 * sum(g1[u] * gp[(f_phi * u) % N] for u in range(1, N, 2))
            C_1 = 2 * sum(g1[u] * gp[u] for u in range(1, N, 2))
            C_invf = 2 * sum(g1[u] * gp[(pow(f_phi, -1, N) * u) % N] for u in range(1, N, 2))
            print(f"    N={N:3d} (N mod {f_phi}={N%f_phi:2d}, phi(N)={phi_fn(N):+d}): C(1)={C_1}, C(f)={C_f}, C(f^-1)={C_invf}")

# =============================================================================
# PART 2: EXACT FINITE MOMENTS OVER K_0 = Q(sqrt(5))
# =============================================================================
def mul_ok(x, y, mod):
    a, b = x
    c, d = y
    return ((a * c - b * d) % mod, (a * d + b * c + 3 * b * d) % mod)

def inv_ok(x, mod):
    a, b = x
    n = (a * a + 3 * a * b + b * b) % mod
    ni = pow(n, -1, mod)
    return (((a + 3 * b) * ni) % mod, ((-b) * ni) % mod)

def W_num(a, b, N):
    return 3 * (2 * a - N) * (2 * b - N) + 9 * (a * a - a * N + b * b - b * N) + 3 * N * N

def B1_num(a, N):
    return 6 * N * (2 * a - N)

def compute_orbit_sums_K0(M, f, phi_table):
    """
    For K_0 = Q(sqrt(5)), modulus M (integer >= 3, gcd(M, f) = 1),
    and totally even phi mod f (if f=1, trivial character!).
    Computes:
      - cosets of H_M = <-1, omega> in U_M = (O_{K0}/M)^*
      - S_phi[coset_idx] = exact Fraction so that for all chi in Cl^+_M(K_0)^-:
          L_{K0}(0, phi * chi) = sum_{c} chi(rep[c]) * S_phi[c]
    """
    eps = (0, 1)      # eps_+
    omega = (-1 % M, 1 % M)
    neg1 = (-1 % M, 0)

    # Enumerate U_M
    U = []
    for a in range(M):
        for b in range(M):
            if math.gcd(a * a + 3 * a * b + b * b, M) == 1:
                U.append((a, b))

    # Build E_M = <eps_+>
    E_M = []
    cur = (1 % M, 0)
    while True:
        E_M.append(cur)
        cur = mul_ok(cur, eps, M)
        if cur == (1 % M, 0):
            break
    E_set = set(E_M)
    neg1_in_E = (neg1 in E_set)
    omega_in_pmE = (omega in E_set) or (mul_ok(neg1, omega, M) in E_set)
    if omega_in_pmE:
        return None  # No totally odd characters mod M!

    # Build H_M = <-1, omega> = E_M u (-E_M) u omega*E_M u (-omega*E_M)
    if neg1_in_E:
        plus_orb = list(E_M)
        minus_orb = [mul_ok(omega, x, M) for x in E_M]
    else:
        plus_orb = list(E_M) + [mul_ok(neg1, x, M) for x in E_M]
        minus_orb = [mul_ok(omega, x, M) for x in E_M] + [mul_ok(neg1, mul_ok(omega, x, M), M) for x in E_M]
    H_set = set(plus_orb) | set(minus_orb)
    assert len(H_set) == len(plus_orb) + len(minus_orb)

    # Decompose U_M into H_M-cosets
    visited = set()
    reps = []
    elem_to_coset_sign = {}  # x -> (coset_idx, +1 or -1) where x in rep * (+1: plus_orb, -1: minus_orb)
    for x in U:
        if x in visited:
            continue
        cidx = len(reps)
        reps.append(x)
        for h in plus_orb:
            y = mul_ok(x, h, M)
            visited.add(y)
            elem_to_coset_sign[y] = (cidx, +1)
        for h in minus_orb:
            y = mul_ok(x, h, M)
            visited.add(y)
            elem_to_coset_sign[y] = (cidx, -1)

    # Compute G_M(u1, u2) for 1 <= u1 <= M, 0 <= u2 <= M-1 (NOTE: cone C(1, eps_+) has x1 > 0, x2 >= 0!)
    # Wait: carefully verify the 1D boundary ray x2 = 0 in Shintani's formula!
    # Cone C(1, eps_+) = R_{>0} * 1 + R_{>=0} * eps_+.
    # In fundamental domain (0, 1] x [0, 1) of Z + Z*eps_+ shifted by N:
    #   - Interior 2D cone: 1 <= x1 <= N, 1 <= x2 <= N, kernel W_N(x1, x2)
    #   - 1D ray (x2 = 0): 1 <= x1 <= N, kernel B_1(x1/N)  (Wait: check sign and ray convention!)
    # Let's check exact convention in test_2d_rayclass_corx.py:
    # For phi with zero row/col sums (f > 1):
    #   G_M(u1, u2) = (1/f^2) sum_{r1, r2=0}^{f-1} r1*r2 * phi((u1+r1*M)%f, (u2+r2*M)%f)
    #   for 1 <= u1 <= M, 1 <= u2 <= M! (And u2=0 mod M corresponds to u2=M, which has same mod f value
    #   ONLY shifted by M! Wait: 1 <= u2 <= M vs 0 <= u2 <= M-1! Let's be 100% EXACT!)
    # For f == 1 (trivial character, phi = 1):
    #   C(1, eps_+) = (0, 1] * 1 + (0, 1] * eps_+  PLUS  (0, 1] * 1 (Wait: NO, if we use (0,1]x(0,1], then
    #   (0,1]*1 is covered by x2=0, which is DIFFERENT from x2=1! Let's check Shintani's exact formula!)
    # Shintani's cone decomposition for K_0:
    #   O_{K0}^+ / <eps_+> = {x1*1 + x2*eps_+ : x1 > 0, x2 >= 0} = (x1 >= 1, x2 >= 1) U (x1 >= 1, x2 = 0).
    #   For x1 >= 1, x2 >= 1: write x1 = u1 + k1*M (1 <= u1 <= M, k1 >= 0), x2 = u2 + k2*M (1 <= u2 <= M, k2 >= 0):
    #     zeta_2(0; u1/M, u2/M) = B_1(u1/M) B_1(u2/M) + (3/4)*(B_2(u1/M) + B_2(u2/M))   [with B_1(x) = x - 1/2, Wait:
    #     at s=0, sum_{k>=0} (k + x)^{-s} = -B_1(x) = 1/2 - x!
    #     Product of two: (-B_1(x1))(-B_1(x2)) = +B_1(x1)B_1(x2)!
    #     And the 1D ray x1 >= 1, x2 = 0 has sum_{k1>=0} (k1 + u1/M)^{-s} -> -B_1(u1/M) at s=0!
    #     Wait: what about B_2 terms? In Shintani's Prop 1 for K_0:
    #       zeta_{C(1, eps_+)}(0; x1, x2) = B_1(x1)B_1(x2) + (1/4)*(eps_+ + eps_+^{-1})*(B_2(x1) + B_2(x2))
    #       WAIT: for (x1, x2) in (0, 1]^2, if x2 = 1 corresponds to u2 = 0 mod M (i.e. x2 = M, 2M, ...),
    #       then adding the 1D ray (x2 = 0, x1 in (0, 1]) shifts u2 = M -> u2 = 0:
    #       Notice B_1(0) = -1/2 = B_1(1) - 1, so B_1(x1)*B_1(0) = B_1(x1)*B_1(1) - B_1(x1),
    #       and B_2(0) = B_2(1) = 1/6!
    #       YES!! Using u1 in {1..M} and u2 in {0..M-1} AUTOMATICALLY COMBINES THE 2D CONE AND 1D RAY!!
    #       CHECK: B_1(x1)*B_1(0) + (3/4)*(B_2(x1)+B_2(0)) = [B_1(x1)*B_1(1) + (3/4)*(B_2(x1)+B_2(1))] - B_1(x1)!!
    #       Let's verify this at M=4 with chi_4 o N and psi_0 (should give L(0, chi_4 o N) = 0? Wait: chi_4 o N is EVEN!
    #       Let's verify at M=11 or M=41 with F^CM_1025 (L = 2) and chi_4 (wait: chi_{-4} on K_0 is NOT chi_4 o N!
    #       Wait: on K_0, N(a + b*e) mod 4: chi_{-4}(N(x)) is TOTALLY EVEN because N(omega) = -1 -> chi_{-4}(-1) = -1,
    #       WAIT A SECOND! chi_{-4}(N(omega)) = chi_{-4}(-1) = -1, so chi_{-4} o N IS TOTALLY ODD!!
    #       And L_{K0}(0, chi_{-4} o N) = L(0, chi_{-4}) * L(0, chi_{-20}) = (1/2) * 2 = 1!!
    #       Let's assert this exact value = 1 in code!)

    if f == 1:
        # G_M(u1, u2) for u1 in 1..M, u2 in 0..M-1 (using 12*M^2 denominator):
        # For u1 in 1..M, u2 in 0..M-1:
        #   W_num(u1, u2, M) / (12 * M^2)
        # Wait: check u2 = 0: W_num(u1, 0, M) = 3*(2u1-M)*(-M) + 9*(u1^2-u1*M) + 3*M^2
        #   Compare with W_num(u1, M, M) - B1_num(u1, M):
        #   W_num(u1, M, M) = 3*(2u1-M)*(M) + 9*(u1^2-u1*M) + 3*M^2
        #   W_num(u1, M, M) - B1_num(u1, M) = 3*(2u1-M)*M - 6*M*(2u1-M) + 9*(u1^2-u1*M) + 3*M^2 = W_num(u1, 0, M)!!
        #   EXACT ALGEBRAIC IDENTITY!!
        denom = 12 * M * M
        def GM(a, b):
            # a in 0..M-1 -> u1 in 1..M; b in 0..M-1 -> u2 in 0..M-1
            u1 = M if a == 0 else a
            u2 = b
            return W_num(u1, u2, M)
        S_phi = [Fraction(0)] * len(reps)
        for cidx, rep in enumerate(reps):
            s = 0
            for h in plus_orb:
                a, b = mul_ok(rep, h, M)
                s += GM(a, b)
            for h in minus_orb:
                a, b = mul_ok(rep, h, M)
                s -= GM(a, b)
            S_phi[cidx] = Fraction(s, denom)
    else:
        # Fast formula for zero row/col sum phi mod f:
        # Careful: in Theorem A01-1, u1 in 1..M, u2 in 0..M-1!
        # Wait: for u2 = 0, x2 = 0 + r2*M (r2 = 0..f-1), and r2=0 is the 1D ray x2=0,
        # which has factor r2=0 anyway! And for r2 >= 1, x2 = r2*M in [1..fM-1] is in the interior!
        # Wait: let's check u2 = 0 vs u2 = M!
        # At u2 = 0: x2 = r2*M (r2 = 0..f-1) runs from 0 to (f-1)M.
        # At u2 = M: x2 = M + r2*M (r2 = 0..f-1) runs from M to fM.
        # Difference is (x2 = 0 with B_1(0) = -1/2) minus (x2 = fM with B_1(1) = +1/2), which is -1 * B_1(x1/N),
        # summed over r1 gives 0 ONLY because row sum = 0!
        # Wait: check B_1(x1/N) * phi(x1, 0): sum_{r1=0}^{f-1} (u1+r1*M)/N * phi(u1+r1*M, 0) is NOT zero!
        # SO u2 MUST BE IN 0..M-1 (i.e. x2 = u2 + r2*M with r2 = 0..f-1, so u2=0 gives x2 = r2*M)!
        # Let's double check: sum_{r1, r2=0}^{f-1} r1*r2 * phi(u1 + r1*M, u2 + r2*M) for u1 in 1..M, u2 in 0..M-1!
        # At u1 = a (1..M), u2 = b (0..M-1), (u1 mod f, u2 mod f):
        #   Wait: if a == 0 mod M, u1 = M, so u1 % f = M % f (NOT 0!)!
        #   If b == 0 mod M, u2 = 0, so u2 % f = 0!
        # LET'S VERIFY THIS BY CALIBRATING AGAINST KNOWN L-VALUES!!
        m0 = M % f
        # Precompute S2[a][b] = sum_{r2=0}^{f-1} r2 * phi(a, (b + r2*m0)%f)
        S2 = [[0] * f for _ in range(f)]
        for a in range(f):
            for b in range(f):
                s = 0
                cur_b = b
                for r2 in range(f):
                    s += r2 * phi_table[a][cur_b]
                    cur_b += m0
                    if cur_b >= f:
                        cur_b -= f
                S2[a][b] = s
        H = [[0] * f for _ in range(f)]
        for a in range(f):
            for b in range(f):
                s = 0
                cur_a = a
                for r1 in range(f):
                    s += r1 * S2[cur_a][b]
                    cur_a += m0
                    if cur_a >= f:
                        cur_a -= f
                H[a][b] = s
        denom = f * f
        S_phi = [Fraction(0)] * len(reps)
        for cidx, rep in enumerate(reps):
            s = 0
            for h in plus_orb:
                a, b = mul_ok(rep, h, M)
                u1 = M if a == 0 else a
                u2 = b
                s += H[u1 % f][u2 % f]
            for h in minus_orb:
                a, b = mul_ok(rep, h, M)
                u1 = M if a == 0 else a
                u2 = b
                s -= H[u1 % f][u2 % f]
            S_phi[cidx] = Fraction(s, denom)

    return reps, elem_to_coset_sign, S_phi

def test_K0_moments():
    print("\n" + "=" * 78)
    print("PART 2: EXACT FINITE SECOND & THIRD MOMENTS OVER K_0 = Q(sqrt(5))")
    print("=" * 78)

    # Calibration check at M = 4!
    # At M = 4, U_4 has order (16-1)=15? No, 2 is inert, (O/4)^* has order 4*(4-1) = 12.
    # eps_+ = (0, 1): eps_+^2 = (-1, 3) = (3, 3), eps_+^3 = (-3, 8) = (1, 0) => ord_4(eps_+) = 3!
    # omega = (3, 1), -1 = (3, 0): |H_4| = 12 => N_cos = 1! Unique totally odd char mod 4 is chi_{-4} o N!
    # Check L_{K0}(0, chi_{-4} o N) = L(0, chi_{-4}) * L(0, chi_{-20}) = (1/2) * 2 = 1!
    # And L_{K0}(0, psi_0 * (chi_{-4} o N)) = 4 (from W2 / A01 calibration)!
    reps4, map4, S1_4 = compute_orbit_sums_K0(4, 1, None)
    assert len(reps4) == 1 and S1_4[0] == Fraction(1), f"Calib 1 failed: {S1_4}"

    phi29 = [[0] * 29 for _ in range(29)]
    phi29_conj = [[0] * 29 for _ in range(29)]
    for a in range(29):
        for b in range(29):
            v1 = (a - 4 * b) % 29
            phi29[a][b] = 0 if v1 == 0 else int(sp.legendre_symbol(v1, 29))
            v2 = (a + 7 * b) % 29
            phi29_conj[a][b] = 0 if v2 == 0 else int(sp.legendre_symbol(v2, 29))

    reps4b, map4b, S29_4 = compute_orbit_sums_K0(4, 29, phi29)
    assert len(reps4b) == 1 and S29_4[0] == Fraction(4), f"Calib 29 failed: {S29_4}"
    print(f"  [K_0 Shintani CALIBRATED: L(0, chi_-4 o N) = {S1_4[0]} == 1, L(0, psi_0 * chi_-4 o N) = {S29_4[0]} == 4!]")

    # Also verify exact L_{K0}(-1, psi_0) for F^+_725?
    # Note: psi_0 is totally even, conductor p_29 (Nm=29), so L_{K0}(-1, psi_0) is a nonzero rational integer (or half-integer).
    # Let's compute finite second moments over Cl^+_M(K_0)^- for M in {7, 11, 13, 17, 19, 21, 31, 34, 41, 55, 61}!
    # For each M, compute:
    #   S_1(u)     for psi = 1
    #   S_29(u)    for psi = psi_0 (F^+_725)
    #   S_29c(u)   for psi = psi_0' (conjugate)
    # And compute:
    #   C_{1, 29}(a)  = (1/|X|) sum_{chi} chi(a) L(0, chi) L(0, psi_0 chi^{-1})
    #                 = sum_{u} S_1(u) * sign(a*u) * S_29(coset(a*u))
    #   C_{29, 29c}(a) = (1/|X|) sum_{chi} chi(a) L(0, psi_0 chi) L(0, psi_0' chi^{-1})
    #   C_{1, 29}^+(a) = (1/|X|) sum_{chi} chi(a) L(0, chi) L(0, psi_0 chi)
    #   T_{1, 29, 29c}(1) = (1/|X|) sum_{chi} L(0, chi) L(0, psi_0 chi^{-1}) L(0, psi_0' chi^{-1})

    print("\n--- 2A: Exact Second Moments C(1) & Max/Nonzero Spectrum over K_0 = Q(sqrt(5)) ---")
    print(f"  {'M':>3} | {'N_cos':>5} | {'C_{1,29}(1)':>14} | {'C_{29,29c}(1)':>14} | {'C_{1,29}^+(1)':>14} | {'T_3(1)':>14} | {'#a: C_{1,29}(a)!=0 (l=3,5,7,11)'}")
    for M in [7, 11, 13, 17, 19, 21, 31, 34, 41, 55]:
        res1 = compute_orbit_sums_K0(M, 1, None)
        if res1 is None:
            continue
        reps, emap, S1 = res1
        _, _, S29 = compute_orbit_sums_K0(M, 29, phi29)
        _, _, S29c = compute_orbit_sums_K0(M, 29, phi29_conj)
        Ncos = len(reps)

        # Compute C(a) for all a in reps:
        C_1_29 = []
        C_29_29c = []
        C_1_29_plus = []
        for a_idx, a in enumerate(reps):
            s12 = Fraction(0)
            s23 = Fraction(0)
            s12p = Fraction(0)
            for u_idx, u in enumerate(reps):
                au = mul_ok(a, u, M)
                v_idx, sgn = emap[au]
                s12 += S1[u_idx] * sgn * S29[v_idx]
                s23 += S29[u_idx] * sgn * S29c[v_idx]
                # For same sign: sum_u S1[u] S29[(a*u)^{-1}]
                au_inv = inv_ok(au, M)
                vi_idx, sgni = emap[au_inv]
                s12p += S1[u_idx] * sgni * S29[vi_idx]
            C_1_29.append(s12)
            C_29_29c.append(s23)
            C_1_29_plus.append(s12p)

        # Triple moment at a = 1: sum_{u, v} S1(u) * S29(v) * S29c(u * v^{-1})
        # Wait: chi(u) chi^{-1}(v) chi^{-1}(w) = 1 => w = u * v^{-1} (up to H_M)!
        T3_1 = Fraction(0)
        if Ncos <= 50:
            for u_idx, u in enumerate(reps):
                for v_idx, v in enumerate(reps):
                    w = mul_ok(u, inv_ok(v, M), M)
                    w_idx, sgn = emap[w]
                    T3_1 += S1[u_idx] * S29[v_idx] * sgn * S29c[w_idx]

        # Count how many a have C_{1,29}(a) != 0 mod ell (for ell coprime to M and Ncos)
        nz_str = []
        for ell in [3, 5, 7, 11]:
            if M % ell == 0 or Ncos % ell == 0:
                nz_str.append(f"{ell}:skip")
            else:
                cnt = sum(1 for x in C_1_29 if (x.denominator % ell != 0 and x.numerator % ell != 0))
                bad_den = sum(1 for x in C_1_29 if x.denominator % ell == 0)
                nz_str.append(f"{ell}:{cnt}/{Ncos}" + (f"(d!{bad_den})" if bad_den else ""))
        print(f"  {M:3d} | {Ncos:5d} | {str(C_1_29[0]):>14} | {str(C_29_29c[0]):>14} | {str(C_1_29_plus[0]):>14} | {str(T3_1):>14} | " + ", ".join(nz_str))

    # Also check: what is C_{1, 29}(a) at a = p_29-related elements?!
    # Wait: p_29 = (4 + eps_+) = (4, 1)!!
    # Let's check C_{1, 29}(a) at a = (4, 1) (the generator of p_29!) and a = (7, -1) (generator of p_29')!
    print("\n--- 2B: Checking C_{1, 29}(a) at a = pi_29 = 4 + eps_+ (the conductor generator of psi_0!) ---")
    # Wait: just like on Q where C(f) matched q * phi(q) * L(-1, phi),
    # on K_0 does C(pi_29) match Nm(M) * psi_0(M) * L_{K0}(-1, psi_0)?!
    for M in [7, 11, 13, 17, 19, 31, 41, 55, 61]:
        res1 = compute_orbit_sums_K0(M, 1, None)
        if res1 is None:
            continue
        reps, emap, S1 = res1
        _, _, S29 = compute_orbit_sums_K0(M, 29, phi29)
        pi29 = (4 % M, 1 % M)
        pi29_inv = inv_ok(pi29, M)
        s_pi = Fraction(0)
        s_pi_inv = Fraction(0)
        for u_idx, u in enumerate(reps):
            v1_idx, sgn1 = emap[mul_ok(pi29, u, M)]
            v2_idx, sgn2 = emap[mul_ok(pi29_inv, u, M)]
            s_pi += S1[u_idx] * sgn1 * S29[v1_idx]
            s_pi_inv += S1[u_idx] * sgn2 * S29[v2_idx]
        # Compute psi_0(M) = legendre(M, 29) (since M is rational!)
        # Wait: psi_0(M O_{K0}) = psi_0(M) = legendre(M, 29)!
        p29M = int(sp.legendre_symbol(M % 29, 29))
        print(f"  M={M:2d} (Nm={M*M:4d}, psi0(M)={p29M:+d}): C(pi_29)={str(s_pi):>16} (val/M^2={float(s_pi)/(M*M):+.5f}), C(pi_29^-1)={str(s_pi_inv):>16} (val/M^2={float(s_pi_inv)/(M*M):+.5f})")

if __name__ == "__main__":
    test_Q_moments()
    test_K0_moments()
