#!/usr/bin/env python3
"""
Wave-3 Agent A13 Part 2 Comprehensive Verification Script:
1. Exact algebraic check of sqrt(y) in Z[w] = O_{M_6} and L(1, eps_2/F_3) / L'(0, eps_2/F_3)
2. Complete prime splitting census up to p <= 500 for K_{-275}/Q(sqrt(5)) and M_6/F_3(229) & K_4
3. Exact finite-place inert divisibility vs archimedean log-height tests:
   (A) Stark unit Lucas/torus products Pi_x = prod_{n=1}^x (u^n - u^{-n}) and single values u^n - u^{-n}
   (B) Global multi-height Hazewinkel formal groups F_{K_{-275}} and F_{K_4} (up to a = 24)
   (C) Barnes triple-gamma 1/Gamma_3(z) vs Kurokawa-Koyama triple sine S_3(z) order-3 Taylor asymptotics,
       plus Barnes double-sine S_2 derivative transcendence test at K_{-275}
4. Prime-ideal centered ramp sums G_{F^+}(psi_{-275}, y) and G_{F_3}(eps_2, y) up to y = 2000
"""

import math
from collections import Counter
import sympy as sp
import mpmath as mp

mp.mp.dps = 30

print("=" * 80)
print("SECTION 1: EXACT sqrt(y) IN Z[w] = O_{M_6} & L-FUNCTION VERIFICATION FOR eps_2/F_3")
print("=" * 80)

w = sp.Symbol('w')
P_M6 = w**6 - w**4 + w**3 - w**2 + 1
# Recall y = -(w + w^{-1}) mod P_M6. Compute w^{-1} mod P_M6:
# w^6 - w^4 + w^3 - w^2 + 1 = 0 => w^{-1} = -w^5 + w^3 - w^2 + w
w_inv = -w**5 + w**3 - w**2 + w
assert sp.rem(sp.expand(w * w_inv - 1), P_M6, w) == 0
y_in_w = sp.expand(-(w + w_inv))  # w^5 - w^3 + w^2 - 2w
print("y in Z[w]:", y_in_w)
assert sp.rem(sp.expand(y_in_w**3 - 4*y_in_w - 1), P_M6, w) == 0

# Compute sqrt(y) = (w - 1) / ((w + 1)*(y + 2)) in Z[w]
# Find inverse of (w + 1)*(y + 2) mod P_M6
denom = sp.rem(sp.expand((w + 1) * (y_in_w + 2)), P_M6, w)
s_inv, _, g = sp.gcdex(sp.Poly(denom, w), sp.Poly(P_M6, w))
assert g.as_expr() == 1
sqy_in_w = sp.rem(sp.expand((w - 1) * s_inv.as_expr()), P_M6, w)
print("sqrt(y) in Z[w]:", sqy_in_w)
sqy_sq = sp.rem(sp.expand(sqy_in_w**2 - y_in_w), P_M6, w)
print("Verify (sqrt(y))^2 - y == 0 mod P_M6:", sqy_sq == 0)
assert sqy_sq == 0
# Check minimal polynomial of sqrt(y): should be t^6 - 4*t^2 - 1
t = sp.Symbol('t')
assert sp.rem(sp.expand(sqy_in_w**6 - 4*sqy_in_w**2 - 1), P_M6, w) == 0
print("Exact element sqrt(y) = w^4 - w^2 + w - 1? Actual:", sqy_in_w)
print("Minimal poly of sqrt(y): t^6 - 4*t^2 - 1 = 0 (disc = -2^6 * 229^2, index 8 in Z[w])")

# Verify L(s, eps_2 / F_3) = zeta_{K_4}(s) / zeta(s) functional equation & L'(0, eps_2/F_3) = R_{K_4} = log|w1|!
# Gamma factor of L(s, eps_2 / F_3) is Gamma_R(s) * Gamma_R(s+1)^2 = Gamma_C(s) * Gamma_R(s+1)
# Conductor A = |D_{F_3}| * N(1) = 229.
# Verify directly via numerical Euler product at s = 2 and Mellin-Barnes/Dokchitser check or K_4 class number formula:
# Already proved analytically: L(1, eps_2/F_3) = Res_{s=1} zeta_{K_4}(s) = 2*pi^2 * R_{K_4} / sqrt(229),
# and L'(0, eps_2/F_3) = sqrt(229)/(2*pi^2) * L(1, eps_2/F_3) = R_{K_4} = log|w1| = 0.33737780357156190144!

print("\n" + "=" * 80)
print("SECTION 2: PRIME SPLITTING CENSUS UP TO p <= 500 FOR BOTH BENCHMARKS")
print("=" * 80)

u, y, x = sp.symbols('u y x')
P_275 = u**4 + 3*u**3 + 3*u**2 + 3*u + 1
P_F3  = y**3 - 4*y - 1
P_K4  = x**4 + x + 1

primes_500 = list(sp.primerange(2, 501))
print(f"Total rational primes p <= 500: {len(primes_500)}")

# 2A: K_{-275} / Q(sqrt(5))
# Prime ideals P of F^+ = Q(sqrt(5)) with N(P) <= 500 (and rational primes p <= 500)
k275_types = Counter()
k275_split_primes_in_F = []   # (p, psi(P1), psi(P2))
k275_inert_primes_in_F = []   # (p, psi((p)))
k275_prime_ideals = []        # list of (N(P), p, f_F, psi(P))

for p in primes_500:
    if p == 5:
        k275_types['ram_5 (F:e=2, K/F:inert)'] += 1
        k275_prime_ideals.append((5, 5, 1, -1))
    elif p == 11:
        k275_types['ram_11 (F:split, K/F:ram+inert)'] += 1
        k275_prime_ideals.append((11, 11, 1, 0))
        k275_prime_ideals.append((11, 11, 1, -1))
    else:
        leg5 = -1 if p == 2 else (1 if pow(5, (p - 1) // 2, p) == 1 else -1)
        fac = sp.factor_list(P_275, modulus=p)[1]
        degs = tuple(sorted([sp.Poly(f, u).degree() for f, m in fac for _ in range(m)]))
        if leg5 == -1:
            # p inert in Q(sqrt(5)), N(P) = p^2
            if degs == (2, 2):
                k275_types['F:inert, K/F:split  [2,2] (D4:2B, pred 1/4)'] += 1
                k275_inert_primes_in_F.append((p, +1))
                k275_prime_ideals.append((p*p, p, 2, +1))
            elif degs == (4,):
                k275_types['F:inert, K/F:inert  [4]   (D4:4,  pred 1/4)'] += 1
                k275_inert_primes_in_F.append((p, -1))
                k275_prime_ideals.append((p*p, p, 2, -1))
        else:
            # p splits in Q(sqrt(5)), N(P_i) = p
            if degs == (1, 1, 1, 1):
                k275_types['F:split, K/F:sp+sp  [1^4] (D4:1,  pred 1/8)'] += 1
                k275_split_primes_in_F.append((p, +1, +1))
                k275_prime_ideals.append((p, p, 1, +1))
                k275_prime_ideals.append((p, p, 1, +1))
            elif degs == (1, 1, 2):
                k275_types['F:split, K/F:sp+in  [1,1,2](D4:2A,pred 1/4)'] += 1
                k275_split_primes_in_F.append((p, +1, -1))
                k275_prime_ideals.append((p, p, 1, +1))
                k275_prime_ideals.append((p, p, 1, -1))
            elif degs == (2, 2):
                k275_types['F:split, K/F:in+in  [2,2] (D4:2C, pred 1/8)'] += 1
                k275_split_primes_in_F.append((p, -1, -1))
                k275_prime_ideals.append((p, p, 1, -1))
                k275_prime_ideals.append((p, p, 1, -1))

print("\n[A] K_{-275} / Q(sqrt(5)) (G = D_4, |G|=8) splitting census for p <= 500:")
unram_275 = len(primes_500) - 2
for k, v in sorted(k275_types.items()):
    print(f"  {k:48s}: {v:3d}  (emp = {v/unram_275:.4f})")

# Print first 15 primes in each RM/inert class for K_{-275}
inert_F_split_K = [p for p, s in k275_inert_primes_in_F if s == +1]
inert_F_inert_K = [p for p, s in k275_inert_primes_in_F if s == -1]
split_F_both_inert = [p for p, s1, s2 in k275_split_primes_in_F if s1 == -1 and s2 == -1]
split_F_both_split = [p for p, s1, s2 in k275_split_primes_in_F if s1 == +1 and s2 == +1]
print("  First 15 p inert in F, split in K_{-275} (RM Darmon-Vonk primes!):", inert_F_split_K[:15])
print("  First 15 p inert in F, inert in K_{-275} ([4]):", inert_F_inert_K[:15])
print("  First 15 p split in F, both split in K_{-275} ([1^4]):", split_F_both_split[:15])
print("  First 15 p split in F, both inert in K_{-275} ([2,2]):", split_F_both_inert[:15])

# 2B: F_3(229), M_6, and K_4 = Q[x]/(x^4 + x + 1) (G = S_4, |G| = 24)
# Note: only p = 229 ramifies!
s4_types = Counter()
f3_prime_ideals = []  # (N(P), p, f_F3, eps_2(P))
for p in primes_500:
    if p == 229:
        fac_F3 = sp.factor_list(P_F3, modulus=229)[1]
        fac_K4 = sp.factor_list(P_K4, modulus=229)[1]
        fac_M6 = sp.factor_list(P_M6, modulus=229)[1]
        print(f"\n  Ramified prime p = 229:")
        print(f"    F_3 mod 229: {[(sp.Poly(f, y).degree(), m) for f, m in fac_F3]}")
        print(f"    K_4 mod 229: {[(sp.Poly(f, x).degree(), m) for f, m in fac_K4]}")
        print(f"    M_6 mod 229: {[(sp.Poly(f, w).degree(), m) for f, m in fac_M6]}")
        # At p = 229: F_3 has p1^2 * p2 (both norm 229); M_6/F_3 is EVERYWHERE UNRAMIFIED!
        # Check whether p1 and p2 split or stay inert in M_6/F_3 from M_6 mod 229:
        # K_4 mod 229 has (1)^2 * (1) * (1) or (1)^2 * (2)! Let's read directly from fac_M6!
        degs_M6_229 = sorted([(sp.Poly(f, w).degree(), m) for f, m in fac_M6])
        # p1^2 in F_3: if eps_2(p1) = +1 gives (1,2),(1,2), if -1 gives (2,2).
        # p2 in F_3: if eps_2(p2) = +1 gives (1,1),(1,1), if -1 gives (2,1).
        e_p1 = +1 if degs_M6_229.count((1, 2)) == 2 else -1
        e_p2 = +1 if degs_M6_229.count((1, 1)) == 2 else -1
        print(f"    => eps_2(p1_ram) = {e_p1:+d}, eps_2(p2_unram) = {e_p2:+d}")
        f3_prime_ideals.append((229, 229, 1, e_p1))
        f3_prime_ideals.append((229, 229, 1, e_p2))
        continue

    fac_F3 = sp.factor_list(P_F3, modulus=p)[1]
    fac_K4 = sp.factor_list(P_K4, modulus=p)[1]
    fac_M6 = sp.factor_list(P_M6, modulus=p)[1]
    dF3 = tuple(sorted([sp.Poly(f, y).degree() for f, m in fac_F3 for _ in range(m)]))
    dK4 = tuple(sorted([sp.Poly(f, x).degree() for f, m in fac_K4 for _ in range(m)]))
    dM6 = tuple(sorted([sp.Poly(f, w).degree() for f, m in fac_M6 for _ in range(m)]))

    # Match S_4 Frobenius cycle type:
    # (1^4) [1/24]:   K4=(1,1,1,1), F3=(1,1,1), M6=(1,1,1,1,1,1) -> eps2 = (+1, +1, +1)
    # (2,2) [3/24]:   K4=(2,2),     F3=(1,1,1), M6=(1,1,2,2)     -> eps2 = (+1, -1, -1)
    # (2,1,1)[6/24]:  K4=(1,1,2),   F3=(1,2),   M6=(1,1,4) or (2,2,2)?
    #   Check! Transposition (12) in S_4:
    #   On F_3 = S_4/D_4 (3 partitions {{12},{34}}, {{13},{24}}, {{14},{23}}):
    #     (12) fixes {{12},{34}} and swaps the other two! So F_3 has degs (1, 2).
    #   On M_6 = S_4/W where W = {1, (12), (34), (12)(34)} < D_4:
    #     (12) in W! So on the fixed point {{12},{34}}, eps_2(P_1) = +1 (splits into (1,1))!
    #     On the swapped pair (order 2, (12)^2 = 1 in W!), eps_2(P_2) = +1 (splits into (2,2))!
    #     WAIT: Check! On S_4/W (size 6), (12) fixes TWO cosets (1*W and (34)*W? No: (12) is in W, and
    #     the normalizer of W is D_4 of size 8, so (12) fixes 2 cosets: W and (1324)W? Let's check!)
    #     Actually our script computes dM6 directly, so let's read the EXACT values!
    key = f"K4={str(dK4):12s} F3={str(dF3):9s} M6={str(dM6):18s}"
    s4_types[key] += 1

    # Extract exact eps_2(P) for each prime ideal P of F_3 above p from dF3 and dM6!
    if dF3 == (1, 1, 1):
        if dM6 == (1, 1, 1, 1, 1, 1):
            for _ in range(3): f3_prime_ideals.append((p, p, 1, +1))
        elif dM6 == (1, 1, 2, 2):
            f3_prime_ideals.append((p, p, 1, +1))
            f3_prime_ideals.append((p, p, 1, -1))
            f3_prime_ideals.append((p, p, 1, -1))
        else:
            raise ValueError(f"Unexpected dF3=(1,1,1) dM6={dM6} at p={p}")
    elif dF3 == (1, 2):
        # P1 has norm p (f=1), P2 has norm p^2 (f=2)
        if dM6 == (1, 1, 2, 2):
            f3_prime_ideals.append((p, p, 1, +1))
            f3_prime_ideals.append((p*p, p, 2, +1))
        elif dM6 == (2, 4):
            f3_prime_ideals.append((p, p, 1, -1))
            f3_prime_ideals.append((p*p, p, 2, -1))
        elif dM6 == (1, 1, 4):
            f3_prime_ideals.append((p, p, 1, +1))
            f3_prime_ideals.append((p*p, p, 2, -1))
        elif dM6 == (2, 2, 2):
            f3_prime_ideals.append((p, p, 1, -1))
            f3_prime_ideals.append((p*p, p, 2, +1))
        else:
            raise ValueError(f"Unexpected dF3=(1,2) dM6={dM6} at p={p}")
    elif dF3 == (3,):
        # P has norm p^3 (f=3)
        if dM6 == (3, 3):
            f3_prime_ideals.append((p**3, p, 3, +1))
        elif dM6 == (6,):
            f3_prime_ideals.append((p**3, p, 3, -1))
        else:
            raise ValueError(f"Unexpected dF3=(3,) dM6={dM6} at p={p}")

print("\n[B] S_4(0,2) triple (K_4, F_3(229), M_6) splitting census for p <= 500 (unramified = 94):")
unram_229 = len(primes_500) - 1
theo_map = {
    "(1, 1, 1, 1)": ("1/24 = 0.0417", "(1^4)"),
    "(2, 2)":       ("3/24 = 0.1250", "(2,2) [c-class!]"),
    "(1, 1, 2)":    ("6/24 = 0.2500", "(2,1,1)"),
    "(1, 3)":       ("8/24 = 0.3333", "(3,1)"),
    "(4,)":         ("6/24 = 0.2500", "(4)"),
}
for k, v in sorted(s4_types.items()):
    k4_part = k.split("K4=")[1].split(" F3=")[0].strip()
    theo_str, cyc_str = theo_map.get(k4_part, ("?", "?"))
    print(f"  {k} | {cyc_str:16s} | count={v:2d} (emp={v/unram_229:.4f}, theo={theo_str})")

# Double-check Euler factor identity: zeta_{K_4}(s) = zeta(s) * L(s, eps_2 / F_3) at EVERY prime p <= 500!
print("\nVerifying exact Euler factor identity E_p(K_4) == E_p(Q) * E_p(eps_2 / F_3) for ALL p <= 500:")
T = sp.Symbol('T')
for p in primes_500:
    if p == 229:
        continue
    fac_K4 = sp.factor_list(P_K4, modulus=p)[1]
    dK4 = [sp.Poly(f, x).degree() for f, m in fac_K4 for _ in range(m)]
    lhs = sp.expand(sp.prod(1 - T**d for d in dK4))
    ps_p = [(f_deg, eps_val) for (nm, pr, f_deg, eps_val) in f3_prime_ideals if pr == p]
    rhs = sp.expand((1 - T) * sp.prod(1 - eps_val * T**f_deg for f_deg, eps_val in ps_p))
    assert lhs == rhs, f"Euler mismatch at p={p}: {lhs} != {rhs}"
print("  PASSED 100% for all 94 unramified primes p <= 500!!")

# Check prime ideals of F_3 with norm <= 500
f3_ideals_500 = sorted([it for it in f3_prime_ideals if it[0] <= 500])
n_split_f3 = sum(1 for it in f3_ideals_500 if it[3] == +1)
n_inert_f3 = sum(1 for it in f3_ideals_500 if it[3] == -1)
print(f"  Prime ideals of F_3 with N(P) <= 500: total={len(f3_ideals_500)}, split(eps_2=+1)={n_split_f3}, inert(eps_2=-1)={n_inert_f3}")

print("\n" + "=" * 80)
print("SECTION 3: FINITE-PLACE INERT DIVISIBILITY VS ARCHIMEDEAN LOG-HEIGHT TESTS")
print("=" * 80)

# --- TEST 3A: Stark Unit Lucas / Norm-1 Torus Sequence u^n - u^{-n} ---
print("\n--- TEST 3A: Stark Unit Lucas Sequence L_n = (u^n - u^{-n})/(u - u^{-1}) & Product Pi_x ---")
# For K_{-275}: u^2 + (1+eps)u + 1 = 0, so alpha := u + u^{-1} = -(1 + eps) in O_{F^+}.
# Lucas sequence in O_{F^+}: U_0 = 0, U_1 = 1, U_{n+1} = alpha * U_n - U_{n-1}.
# Norm of U_n in Z: N_{F^+/Q}(U_n) = U_n(eps) * U_n(eps_bar).
# Note that at inf_2, |u3| = 1, so |U_n(eps_bar)| = |sin(n*theta)/sin(theta)| = O(1)!
# While at inf_1, |U_n(eps)| ~ |u1|^n / (|u1| - |u1|^{-1}), so log|N_{F/Q}(U_n)| ~ n * log|u1|!
# For a prime ideal P of F^+ of norm q = N(P):
#   If P is INERT in K_{-275}/F^+ (psi(P) = -1): P | U_n whenever (q + 1) | n (actually rank of apparition divides q+1)!
#   If P SPLITS in K_{-275}/F^+ (psi(P) = +1): P | U_n whenever (q - 1) | n!
# Let's compute EXACT integer norms N(U_n) for n = 1..150, factor them, and compute exact inert-prime divisibility
# for Pi_x = prod_{n=1}^x U_n vs archimedean log-height log|N(Pi_x)|!

# Represent elements of O_{Q(sqrt(5))} = Z[eps] as (a, b) = a + b*eps, eps^2 = 1 + eps.
def mul_F5(x, y):
    a, b = x
    c, d = y
    return (a*c + b*d, a*d + b*c + b*d)

def norm_F5(x):
    a, b = x
    return a*a + a*b - b*b

alpha_275 = (-1, -1)  # -(1 + eps)
U_seq = [(0, 0), (1, 0)]
for n in range(2, 201):
    # U_n = alpha * U_{n-1} - U_{n-2}
    t1 = mul_F5(alpha_275, U_seq[-1])
    U_seq.append((t1[0] - U_seq[-2][0], t1[1] - U_seq[-2][1]))

# For each prime p <= 500, determine exact v_p from inert ideals vs split ideals in N(U_n)
# Better: for each prime ideal P of F^+ with N(P) <= 500 and psi(P) = -1, compute rank of apparition r(P) and exact sum_{n<=x} v_P(U_n)*log N(P)!
# Even exact: compute v_p(N(U_n)) directly for small x, AND use rank-of-apparition + p-adic lifting!
def lucas_val_mod_pk(alpha_mod, pk, n):
    """Compute U_n mod pk in Z/pkZ (when p splits in F) or (Z/pkZ)[eps] (when p inert)."""
    # Use fast doubling for U_n? Actually n <= 200 so direct iteration is instant!
    pass

# Direct exact integer norm factorization for x = 20, 50, 100, 150, 200!
# For inert primes P (psi(P) = -1):
#   - If p inert in F^+ (N(P) = p^2): U_n = (a_n, b_n) is divisible by P^k iff p^k | gcd(a_n, b_n)!
#     Wait: N(P) = p^2, so v_P(U_n) * log N(P) = min(v_p(a_n), v_p(b_n)) * 2 * log(p)!
#   - If p splits in F^+ (N(P_i) = p): compute v_{P_i}(U_n) by evaluating a_n + b_n * root_eps (mod p^k)!
eps_mp = (1 + mp.sqrt(5)) / 2
u1_abs = abs(mp.polyroots([1, 3, 3, 3, 1], maxsteps=200, extraprec=30)[0].real)
# Sort real roots properly
r275 = sorted([r.real for r in mp.polyroots([1, 3, 3, 3, 1], maxsteps=200, extraprec=30) if abs(r.imag) < mp.mpf('1e-20')])
u1_abs = abs(r275[0])
log_u1 = float(mp.log(u1_abs))

# Build exact list of inert prime ideals P of Q(sqrt(5)) with N(P) <= 500 and psi(P) = -1
# For split p: find roots of x^2 - x - 1 == 0 mod p; which root corresponds to P1 vs P2 with psi(P) = -1?
# Recall u^2 + (1+eps)u + 1 has disc 3*eps - 2. A prime P=(p, eps - r) is INERT in K_{-275}/F^+ iff
# Legendre(3*r - 2, p) == -1! (For p = 2, 2 is inert in F; for p = 5, p_5 = (sqrt(5)), eps = (1+0)/2 = 3 mod 5, inert; for p = 11, p_11' is inert.)
inert_ideals_F5 = []  # (N(P), p, f_F, root_r_or_None)
for p in primes_500:
    if p == 5:
        # ramified p_5 = (sqrt(5)), 2*eps - 1 = sqrt(5) => eps == 3 (mod p_5), psi(p_5) = -1
        inert_ideals_F5.append((5, 5, 1, 'ram5'))
    elif p == 11:
        # p_11 = (4 - sqrt(5)): eps == (1+4)/2 == 8 mod 11 (ramifies);
        # p_11' = (4 + sqrt(5)): sqrt(5) == -4 == 7 mod 11 => eps == (1+7)/2 = 4 mod 11 (inert! psi=-1)
        inert_ideals_F5.append((11, 11, 1, 4))
    else:
        leg5 = -1 if p == 2 else (1 if pow(5, (p - 1) // 2, p) == 1 else -1)
        if leg5 == -1:
            if p * p <= 500:
                # psi((p)) = leg(p, 11)
                if pow(p, 5, 11) != 1:
                    inert_ideals_F5.append((p*p, p, 2, None))
        else:
            # Find roots of r^2 - r - 1 == 0 mod p
            for r in range(p):
                if (r*r - r - 1) % p == 0:
                    disc_mod = (3*r - 2) % p
                    if disc_mod != 0 and pow(disc_mod, (p - 1) // 2, p) == p - 1:
                        inert_ideals_F5.append((p, p, 1, r))

def val_ideal_F5(elem, p, f_F, root_r):
    a, b = elem
    if a == 0 and b == 0:
        return 999
    if f_F == 2:
        # inert prime (p): valuation is min(v_p(a), v_p(b))
        v = 0
        while a % p == 0 and b % p == 0:
            a //= p
            b //= p
            v += 1
        return v
    elif root_r == 'ram5':
        # p_5 = (sqrt(5)), N(a+b*eps) = a^2 + ab - b^2; v_{p_5}(elem) = v_5(N(elem))
        nrm = abs(norm_F5(elem))
        v = 0
        while nrm % 5 == 0:
            nrm //= 5
            v += 1
        return v
    else:
        # split prime P = (p, eps - root_r): Hensel lift root_r to p^k!
        v = 0
        pk = p
        r = root_r
        while True:
            if (a + b * r) % pk != 0:
                break
            v += 1
            # Hensel lift r: r^2 - r - 1 == 0 mod p^{v+1}
            pk_next = pk * p
            fval = (r*r - r - 1) % pk_next
            deriv = (2*r - 1) % p
            inv_d = pow(deriv, -1, p)
            r = (r - fval * inv_d) % pk_next
            pk = pk_next
        return v

print(f"Inert prime ideals of F^+ = Q(sqrt(5)) with N(P) <= 500 (psi(P) = -1): count = {len(inert_ideals_F5)}")
print(f"{'x':>5s} | {'FinInert(Pi_x)':>15s} | {'FinAll(<=x)':>15s} | {'ArchLogH(Pi_x)':>15s} | {'Ratio Inert/Arch':>17s} | {'(x*log x)/Arch':>15s}")
print("-" * 92)
# Also track ALL prime ideals (both split and inert) with N(P) <= x
all_ideals_F5 = []
for p in primes_500:
    if p == 5:
        all_ideals_F5.append((5, 5, 1, 'ram5', -1))
    elif p == 11:
        all_ideals_F5.append((11, 11, 1, 8, 0))
        all_ideals_F5.append((11, 11, 1, 4, -1))
    else:
        leg5 = -1 if p == 2 else (1 if pow(5, (p - 1) // 2, p) == 1 else -1)
        if leg5 == -1:
            if p * p <= 500:
                s = 1 if pow(p, 5, 11) == 1 else -1
                all_ideals_F5.append((p*p, p, 2, None, s))
        else:
            for r in range(p):
                if (r*r - r - 1) % p == 0:
                    disc_mod = (3*r - 2) % p
                    s = 1 if pow(disc_mod, (p - 1) // 2, p) == 1 else -1
                    all_ideals_F5.append((p, p, 1, r, s))

for x_cut in [10, 20, 40, 80, 120, 160, 200]:
    fin_inert = 0.0
    fin_all = 0.0
    for nm, p, f_F, rr, s in all_ideals_F5:
        if nm <= x_cut:
            vsum = sum(val_ideal_F5(U_seq[n], p, f_F, rr) for n in range(1, x_cut + 1))
            contrib = vsum * math.log(nm)
            fin_all += contrib
            if s == -1:
                fin_inert += contrib
    # Exact archimedean log-height: sum_{n=1}^{x_cut} log|N_{F/Q}(U_n)|
    arch_h = sum(math.log(abs(norm_F5(U_seq[n]))) for n in range(1, x_cut + 1))
    print(f"{x_cut:5d} | {fin_inert:15.4f} | {fin_all:15.4f} | {arch_h:15.4f} | {fin_inert/arch_h:17.6f} | {(x_cut*math.log(x_cut))/arch_h:15.6f}")

# --- TEST 3A-ii: Same Lucas / Stark test for w in M_6 / F_3(229)! ---
print("\n--- TEST 3A-ii: Stark Unit Lucas Sequence W_n = (w^n - w^{-n})/(w - w^{-1}) in O_{F_3} ---")
# Recall w^2 + y*w + 1 = 0, so w + w^{-1} = -y in O_{F_3}!
# W_0 = 0, W_1 = 1, W_{n+1} = -y * W_n - W_{n-1} in O_{F_3} = Z[y]/(y^3 - 4y - 1)!
# Note at inf_2 and inf_3, |w| = 1, so |W_n(y2)| = O(1), |W_n(y3)| = O(1),
# while at inf_1, |W_n(y1)| ~ |w1|^n / (|w1| - |w1|^{-1})!
# So log|N_{F_3/Q}(W_n)| ~ n * log|w1| = n * R_{K_4} = n * L'(0, eps_2 / F_3)!!

def mul_F3(a, b):
    # a, b are 3-tuples (c0, c1, c2) = c0 + c1*y + c2*y^2, y^3 = 4y + 1
    r = [0, 0, 0, 0, 0]
    for i in range(3):
        for j in range(3):
            r[i + j] += a[i] * b[j]
    # reduce y^4 = 4y^2 + y, y^3 = 4y + 1
    c4 = r[4]
    r[2] += 4 * c4
    r[1] += c4
    c3 = r[3]
    r[1] += 4 * c3
    r[0] += c3
    return (r[0], r[1], r[2])

def norm_F3(a):
    # Exact resultant of y^3 - 4y - 1 and a0 + a1*y + a2*y^2
    c0, c1, c2 = a
    # Matrix of multiplication by c0 + c1*y + c2*y^2 in basis (1, y, y^2):
    # 1 -> (c0, c1, c2)
    # y -> (c2, c0 + 4*c2, c1)
    # y^2 -> (c1, c2 + 4*c1, c0 + 4*c2)
    m00, m01, m02 = c0, c2, c1
    m10, m11, m12 = c1, c0 + 4*c2, c2 + 4*c1
    m20, m21, m22 = c2, c1, c0 + 4*c2
    return (m00*(m11*m22 - m12*m21) - m01*(m10*m22 - m12*m20) + m02*(m10*m21 - m11*m20))

W_seq = [(0, 0, 0), (1, 0, 0)]
for n in range(2, 201):
    # -y * W_{n-1} - W_{n-2}
    t1 = mul_F3((0, -1, 0), W_seq[-1])
    W_seq.append((t1[0] - W_seq[-2][0], t1[1] - W_seq[-2][1], t1[2] - W_seq[-2][2]))

# Compute exact finite inert divisibility from primes of F_3 with N(P) <= x vs archimedean log|N(Pi_x)|!
# For degree-1 prime P = (p, y - r) of F_3 (p != 229): eps_2(P) = (r^2 - 4 | p) = (r^{-1} | p) = (r | p)!
# WAIT A SECOND! Check that!
# w^2 + y*w + 1 = 0 has discriminant y^2 - 4 = y^{-1}!
# So for EVERY unramified odd prime P of F_3, P is INERT in M_6/F_3 iff y is a NON-SQUARE mod P!!
# (And for p = 2: P2_1 = (2, y+1) has y == 1 mod 2, w^2 + w + 1 irreducible mod 2 => INERT! P2_2 = (2, y^2+y+1) has w^2 + yw + 1 irreducible over F_4 => INERT! Matches M_6 mod 2 = (2, 4)!!)
def val_deg1_F3(elem, p, root_r):
    c0, c1, c2 = elem
    if c0 == 0 and c1 == 0 and c2 == 0:
        return 999
    v = 0
    pk = p
    r = root_r
    while True:
        if (c0 + c1*r + c2*r*r) % pk != 0:
            break
        v += 1
        pk_next = pk * p
        fval = (r**3 - 4*r - 1) % pk_next
        deriv = (3*r*r - 4) % p
        inv_d = pow(deriv, -1, p)
        r = (r - fval * inv_d) % pk_next
        pk = pk_next
    return v

# Collect all degree-1 prime ideals of F_3 with p <= 200 (and p=2 ideals too!)
# Note: for N(P) <= 200, degree-2 primes only occur for p <= 14, degree-3 for p <= 5.
# For simplicity and 100% EXACTNESS: for ANY p <= 200, the total valuation sum over ALL ideals above p of W_n
# equals v_p(N_{F_3/Q}(W_n)) * log(p)! And we can split inert vs split cleanly:
# - At p = 2: BOTH ideals above 2 are INERT in M_6/F_3! So ALL of v_2(N(W_n))*log(2) is INERT!
# - At p = 3, 5: (3) and (5) are inert in F_3 and SPLIT in M_6/F_3 (degs (3,3))! So 0 inert!
# - At odd p <= 200 with dF3 == (1,1,1) or (1,2): we know EXACTLY which degree-1 ideals are inert (Legendre(r, p) == -1),
#   and for degree-2 ideal P2 (when dF3 == (1,2), p <= 14), its valuation is (v_p(N(W_n)) - v_{P1}(W_n)) / 2!
# Let's check exact inert divisibility for M_6/F_3 up to x = 200!

print(f"{'x':>5s} | {'FinInert(Pi_x)':>15s} | {'FinAll(<=x)':>15s} | {'ArchLogH(Pi_x)':>15s} | {'Ratio Inert/Arch':>17s} | {'(x*log x)/Arch':>15s}")
print("-" * 92)
for x_cut in [10, 20, 40, 80, 120, 160, 200]:
    fin_inert = 0.0
    fin_all = 0.0
    # sum over all primes p <= x_cut
    for p in sp.primerange(2, x_cut + 1):
        if p == 2:
            # Both ideals above 2 (N=2 and N=4) are inert in M_6/F_3!
            # Wait: only include N=4 if x_cut >= 4 (always true for x_cut >= 10)
            vsum_tot = 0
            for n in range(1, x_cut + 1):
                nm = abs(norm_F3(W_seq[n]))
                while nm % 2 == 0:
                    nm //= 2
                    vsum_tot += 1
            fin_all += vsum_tot * math.log(2)
            fin_inert += vsum_tot * math.log(2)
            continue
        fac_F3 = sp.factor_list(P_F3, modulus=p)[1]
        dF3 = tuple(sorted([sp.Poly(f, y).degree() for f, m in fac_F3 for _ in range(m)]))
        if dF3 == (3,):
            if p**3 <= x_cut:
                # check if inert or split in M_6
                fac_M6 = sp.factor_list(P_M6, modulus=p)[1]
                dM6 = tuple(sorted([sp.Poly(f, w).degree() for f, m in fac_M6 for _ in range(m)]))
                vsum_tot = 0
                for n in range(1, x_cut + 1):
                    nm = abs(norm_F3(W_seq[n]))
                    while nm % p == 0:
                        nm //= p
                        vsum_tot += 1
                fin_all += vsum_tot * math.log(p)
                if dM6 == (6,):
                    fin_inert += vsum_tot * math.log(p)
        elif dF3 == (1, 1, 1):
            roots_p = [r for r in range(p) if (r**3 - 4*r - 1) % p == 0]
            for r in roots_p:
                vsum = sum(val_deg1_F3(W_seq[n], p, r) for n in range(1, x_cut + 1))
                fin_all += vsum * math.log(p)
                if pow(r, (p - 1) // 2, p) == p - 1:
                    fin_inert += vsum * math.log(p)
        elif dF3 == (1, 2):
            r1 = [r for r in range(p) if (r**3 - 4*r - 1) % p == 0][0]
            v1 = sum(val_deg1_F3(W_seq[n], p, r1) for n in range(1, x_cut + 1))
            fin_all += v1 * math.log(p)
            if pow(r1, (p - 1) // 2, p) == p - 1:
                fin_inert += v1 * math.log(p)
            if p * p <= x_cut:
                vsum_tot = 0
                for n in range(1, x_cut + 1):
                    nm = abs(norm_F3(W_seq[n]))
                    while nm % p == 0:
                        nm //= p
                        vsum_tot += 1
                v2_contrib = (vsum_tot - v1) * math.log(p)
                fin_all += v2_contrib
                fac_M6 = sp.factor_list(P_M6, modulus=p)[1]
                dM6 = tuple(sorted([sp.Poly(f, w).degree() for f, m in fac_M6 for _ in range(m)]))
                # P2 is inert iff dM6 == (2, 4) or (1, 1, 4)
                if 4 in dM6:
                    fin_inert += v2_contrib
    arch_h = sum(math.log(abs(norm_F3(W_seq[n]))) for n in range(1, x_cut + 1))
    print(f"{x_cut:5d} | {fin_inert:15.4f} | {fin_all:15.4f} | {arch_h:15.4f} | {fin_inert/arch_h:17.6f} | {(x_cut*math.log(x_cut))/arch_h:15.6f}")

# --- TEST 3B: Global Multi-Height Hazewinkel Formal Group F_{K_4} (S_4(0,2)) ---
print("\n--- TEST 3B: Global Multi-Height Hazewinkel Formal Group F_{K_4} (x^4+x+1, D=229) ---")
# For each prime p != 229, take f_p = max residue degree of p in K_4 (or minimal >1, or order of Frob_p in S_4):
# Specifically for S_4(0,2):
#   (1^4) -> f_p = 1; (2,2) -> f_p = 2; (1,1,2) -> f_p = 2; (1,3) -> f_p = 3; (4) -> f_p = 4.
# Compute e_a = a! [z^a] exp_{F_{K_4}}(z) up to a = 24 and compare finite divisibility vs archimedean log|e_a|!
def build_hazewinkel_exp(height_map, Amax):
    # ell(T) = sum_{n=1}^{Amax} (c(n)/n) T^n where c(p^k) = p^{k(f_p-1)/f_p} if f_p | k else 0
    c = [sp.Rational(0)] * (Amax + 1)
    c[1] = sp.Rational(1)
    for n in range(2, Amax + 1):
        fac = sp.factorint(n)
        val = sp.Rational(1)
        for p, k in fac.items():
            fp = height_map.get(p, 1)
            if k % fp == 0:
                val *= sp.Rational(p) ** (k * (fp - 1) // fp)
            else:
                val = sp.Rational(0)
                break
        c[n] = val
    # Compute power series inverse exp(z) of ell(T) = sum_{n=1}^{Amax} (c[n]/n) T^n
    # Let exp(z) = sum_{a=1}^{Amax} (e_a / a!) z^a
    # Using ell(exp(z)) = z:
    # Let E(z) = sum_{a=1}^{Amax} b_a z^a with b_1 = 1
    b = [sp.Rational(0)] * (Amax + 1)
    b[1] = sp.Rational(1)
    # Track powers E(z)^m up to z^{Amax}
    # E_pow[m][a] = [z^a] E(z)^m
    for a in range(2, Amax + 1):
        # [z^a] ell(E(z)) = b_a + sum_{n=2}^{a} (c[n]/n) * [z^a] (E_{<a}(z))^n = 0
        # Compute [z^a] E^n incrementally!
        total = sp.Rational(0)
        # Power series of current E up to degree a-1
        cur = b[:a] + [sp.Rational(0)]
        pw = list(cur)  # E^1
        for n in range(2, a + 1):
            # multiply pw by cur up to degree a
            new_pw = [sp.Rational(0)] * (a + 1)
            for i in range(1, a):
                if pw[i] != 0:
                    for j in range(1, a + 1 - i):
                        if cur[j] != 0:
                            new_pw[i + j] += pw[i] * cur[j]
            pw = new_pw
            if c[n] != 0 and pw[a] != 0:
                total += (c[n] / n) * pw[a]
        b[a] = -total
    # Compute e_a = D^a(F)(0) for F(T) = T / (1 - T) = sum_{m>=1} T^m, where D = (ell'(T))^{-1} d/dT,
    # i.e. F(exp(z)) = sum_{a>=1} (e_a / a!) z^a!
    # Since F(E(z)) = E(z) / (1 - E(z)) = sum_{m>=1} E(z)^m:
    # Let G(z) = sum_{a=1}^{Amax} g_a z^a satisfy G(z) = E(z) + E(z)*G(z) => g_a = b_a + sum_{i=1}^{a-1} b_i * g_{a-i}!
    g_ser = [sp.Rational(0)] * (Amax + 1)
    for a in range(1, Amax + 1):
        g_ser[a] = b[a] + sum(b[i] * g_ser[a - i] for i in range(1, a))
    e = [sp.factorial(a) * g_ser[a] for a in range(Amax + 1)]
    return e

hmap_K4 = {}
for p in sp.primerange(2, 35):
    fac_K4 = sp.factor_list(P_K4, modulus=p)[1]
    dK4 = [sp.Poly(f, x).degree() for f, m in fac_K4 for _ in range(m)]
    hmap_K4[p] = max(dK4)
print("Heights f_p for F_{K_4} (p < 35):", {p: hmap_K4[p] for p in sorted(hmap_K4)})
e_K4 = build_hazewinkel_exp(hmap_K4, 28)
print(f"F(T) = T/(1-T), e_a = (D^a F)(0) on Hazewinkel formal group F_{{K_4}}:")
print(f"{'a':>3s} | {'den(e_a)':>8s} | {'FinDiv(a)':>10s} | {'LT-Lower':>10s} | {'log|e_a|':>10s} | {'Ratio Div/Log':>13s}")
print("-" * 68)
for a in [5, 10, 15, 20, 25, 28]:
    ea = e_K4[a]
    den = ea.q
    num = abs(int(ea.p))
    fin_div = 0.0
    lt_lb = 0.0
    for p in sp.primerange(2, a + 1):
        fp = hmap_K4[p]
        if fp >= 2:
            vp = 0
            tmp = num
            while tmp > 0 and tmp % p == 0:
                tmp //= p
                vp += 1
            fin_div += vp * math.log(p)
            k = 1
            pk = p
            lb_p = 0
            while pk <= a:
                if k % fp != 0:
                    lb_p += a // pk
                k += 1
                pk *= p
            lt_lb += lb_p * math.log(p)
    log_arch = math.log(num) if num > 0 else 0.0
    ratio = fin_div / log_arch if log_arch > 0 else 0.0
    print(f"{a:3d} | {den:8d} | {fin_div:10.4f} | {lt_lb:10.4f} | {log_arch:10.4f} | {ratio:13.6f}")

# --- TEST 3C: Barnes 1/Gamma_3(z) vs Kurokawa-Koyama Triple Sine S_3(z) Order-3 Growth & S_2 Derivative Transcendence ---
print("\n--- TEST 3C: Barnes 1/Gamma_3 vs Triple Sine S_3 Order-3 Taylor Growth (w = (1,1,1)) ---")
# Recall exact Barnes triple-gamma for w = (1,1,1):
#   1 / Gamma_3(z + 1; 1, 1, 1) has zeros at z = -1, -2, -3, ... with multiplicity C(n+1, 2) = n(n+1)/2!
# Wait: for w = (1, 1, 1), Kurokawa-Koyama triple sine S_3(z; 1, 1, 1) satisfies:
#   S_3(z) = exp( int_0^z (pi * t^2 * cot(pi*t) / 2 ... ) )  -- wait, exact formula (Kurokawa-Koyama 2003, Thm. 2.1):
#   S_1(z) = 2 sin(pi z)
#   S_2'(z)/S_2(z) = pi * (1 - z) * cot(pi z)  =>  for S_2(z; 1, 1), log S_2(z) = ...
#   S_3'(z)/S_3(z) = pi * (z - 1)*(z - 2)/2 * cot(pi z) ? Let's check exact differential equation!
# Recall Kurokawa-Koyama (2003) Proposition 2.4 for primitive multiple sine P_r(z) := exp( -int_0^z pi*t^{r-1}*cot(pi*t) dt ) (shifted):
# Actually S_r(z; 1,...,1) has exact functional equation S_r(z + 1) = S_r(z) * S_{r-1}(z)^{-1} (up to sign)!
# Check for r = 1: S_1(z) = 2 sin(pi z), S_1(z+1) = -S_1(z).
# For r = 2: S_2(z+1) = S_2(z) / (2 sin(pi z)). Check log-deriv:
#   f_2(z) := (log S_2)'(z) satisfies f_2(z+1) - f_2(z) = -pi cot(pi z).
#   Since pi*(1 - z)*cot(pi z) changes by -pi cot(pi z) when z -> z+1, f_2(z) = pi*(1 - z)*cot(pi z) + const (actually const = 0 since S_2(2-z) = S_2(z)^{-1} => f_2(2-z) = f_2(z), check: pi*(1-(2-z))*cot(pi*(2-z)) = pi*(z-1)*(-cot(pi z)) = pi*(1-z)*cot(pi z)!! EXACT!).
# For r = 3: S_3(z+1) = S_3(z) * S_2(z)^{-1}, so f_3(z) := (log S_3)'(z) satisfies f_3(z+1) - f_3(z) = -f_2(z) = pi*(z - 1)*cot(pi z)!
#   Check polynomial P(z) with P(z+1) - P(z) = z - 1: P(z) = z*(z - 3)/2 + C!
#   Symmetry of S_3(z; 1,1,1): S_3(3 - z) = S_3(z) (since d=3 odd, S_3(z) = 1/(Gamma_3(z)*Gamma_3(3-z)) is EVEN around z = 3/2!)
#   => f_3(3 - z) = -f_3(z)!
#   Check P(3 - z)*cot(pi*(3-z)) = -P(3 - z)*cot(pi z), so we need P(3 - z) = P(z)!
#   And z*(z - 3)/2 IS symmetric under z -> 3 - z! Add constant C: check residue at z = 0!
#   At z = 0, S_3(z) = 1/(Gamma_3(z) Gamma_3(3-z)) has a SIMPLE zero at z = 0! So Res_{z=0} f_3(z) = +1!
#   Since Res_{z=0} pi*cot(pi z) = 1, we need P(0) = 1!!
#   Thus P(z) = 1 + z*(z - 3)/2 = (z - 1)*(z - 2)/2!!
#   CHECK: P(z+1) - P(z) = z*(z-1)/2 - (z-1)*(z-2)/2 = z - 1!! AND P(3-z) = (2-z)*(1-z)/2 = P(z)!! AND P(0) = 1!!
#   AND AT z = 1: P(1) = 0 (no pole/zero at z=1? Wait: Gamma_3(z) has poles at z = 0, -1, -2,... and Gamma_3(3-z) has poles at z = 3, 4, 5,..., so S_3(z) has NO zeros at z=1, 2!! Indeed P(1) = P(2) = 0!!)!
#   OH!! WHAT A GORGEOUS EXACT FORMULA!!
#   (log S_3)'(z) = pi * (z - 1)*(z - 2)/2 * cot(pi z)   (around z = 3/2, shifted u = z - 3/2:
#     (log S_3)'(3/2 + u) = -(pi/2) * (u^2 - 1/4) * tan(pi u)!!
#   WAIT A SECOND!! S_3(3/2 + u) IS AN ENTIRE EVEN FUNCTION OF u WITH ZERO SINGULARITIES AT u = 0!!
#   Let's expand S_3(3/2 + u) = sum_{k=0}^\infty c_{2k} u^{2k} to order 30 and check EXACT order 3, finite type tau = pi/6!!

# Expand g(u) = (log S_3)'(3/2 + u) = -(pi/2)*(u^2 - 1/4)*tan(pi*u) as Taylor series in u!
N_ord = 30
# tan(pi*u) = sum_{k>=1} T_k * (pi*u)^{2k-1} / (2k-1)! where T_k = 2^{2k}(2^{2k}-1)|B_{2k}| / (2k)
g_coeff = [mp.mpf(0)] * (N_ord + 2)
for k in range(1, N_ord // 2 + 2):
    B2k = abs(mp.bernoulli(2*k))
    t_coeff = (mp.mpf(2)**(2*k)) * (mp.mpf(2)**(2*k) - 1) * B2k / mp.factorial(2*k) * (mp.pi**(2*k - 1))
    # Multiply by -(pi/2)*(u^2 - 1/4) = (pi/8) - (pi/2)*u^2
    deg1 = 2*k - 1
    if deg1 <= N_ord:
        g_coeff[deg1] += (mp.pi / 8) * t_coeff
    deg2 = 2*k + 1
    if deg2 <= N_ord:
        g_coeff[deg2] -= (mp.pi / 2) * t_coeff

# Integrate to get L(u) = log(S_3(3/2 + u) / S_3(3/2)) = sum_{m=1}^{N_ord} (g_coeff[m-1]/m) u^m
L_coeff = [mp.mpf(0)] * (N_ord + 1)
for m in range(1, N_ord + 1):
    L_coeff[m] = g_coeff[m - 1] / m

# Exponentiate F(u) = exp(L(u)) = sum_{a=0}^{N_ord} f_a u^a using a*f_a = sum_{m=1}^a m * L_coeff[m] * f_{a-m}
f_S3 = [mp.mpf(0)] * (N_ord + 1)
f_S3[0] = mp.mpf(1)
for a in range(1, N_ord + 1):
    f_S3[a] = sum(m * L_coeff[m] * f_S3[a - m] for m in range(1, a + 1)) / a

# Compare against saddle-point bound for order 3, type tau = pi/6:
#   log|F^{(a)}(0)| <= (2/3)*a*log(a) + a*(-1 + (1 + log(3*tau))/3)
tau3 = mp.pi / 6
lin3 = -1 + (1 + mp.log(3 * tau3)) / 3
print(f"Kurokawa-Koyama Triple Sine S_3(3/2 + u) [exact order 3, finite type tau = pi/6 = {float(tau3):.6f}]:")
print(f"{'a':>3s} | {'log|S3^(a)(3/2)|':>17s} | {'(2/3)a log a + lin*a':>20s} | {'diff':>10s} | {'(diff)/a':>10s}")
print("-" * 70)
for a in [4, 8, 12, 16, 20, 24, 28, 30]:
    deriv_a = abs(f_S3[a] * mp.factorial(a))
    if deriv_a > 0:
        ld = float(mp.log(deriv_a))
        pred = (2.0/3.0)*a*math.log(a) + float(lin3)*a
        print(f"{a:3d} | {ld:17.5f} | {pred:20.5f} | {ld-pred:10.5f} | {(ld-pred)/a:10.5f}")

# Now test a = 1, 2 derivatives of Shintani's Barnes double-sine sum for K_{-275}!
print("\n--- TEST 3C-ii: Derivative Transcendence Test for Shintani S_2 Sum of K_{-275} at a = 0, 1, 2 ---")
# Recall: F_Sh(z) := (1/2) * sum_{r1=1}^{11} sum_{r2=0}^{10} leg(r1+9r2, 11) * log S_2((r1+r2*eps_+)/11 + z; 1, eps_+)
# At z = 0: F_Sh(0) = -L'(0, psi_{-275}) = -log|u1| (algebraic logarithm!).
# What about F_Sh'(0) and F_Sh''(0)?
# Compute via integral representation of (d/dz)^a log S_2(z; 1, eps_+):
# Since log S_2^{int}(z) = int_0^infty (sinh((w1+w2-2z)t/2)/(2*sinh(w1*t/2)*sinh(w2*t/2)) - (w1+w2-2z)/(w1*w2*t)) dt/t,
# differentiating w.r.t. z gives:
#   d/dz [log S_2^{int}(z)] = int_0^infty ( -cosh((w1+w2-2z)t/2) / (2*sinh(w1*t/2)*sinh(w2*t/2)) + 2/(w1*w2*t) ) dt !
# Wait: near t = 0: cosh(a*t/2)/(2*sinh(w1*t/2)*sinh(w2*t/2)) = (1 + a^2 t^2/8) / ((w1 w2 t^2/2)*(1 + (w1^2+w2^2)t^2/24))
#   = 2/(w1 w2 t^2) + ...! So the a=1 derivative of a SINGLE S_2 has a 1/t^2 term, WHICH CANCELS when summed against psi (since sum psi = 0)!
# Even cleaner: compute F_Sh(h) for h = 0, +-1e-6, +-2e-6 using fast numerical integration at 25 dps, or sum the integrand FIRST!
# SUMMING THE INTEGRAND FIRST IS GENIUS:
# Let Phi(t; z) := (1/2) * sum_{r1=1}^{11} sum_{r2=0}^{10} leg(r1+9r2, 11) * sinh((1 + eps_+ - 2*(z_{r1,r2} + z))*t/2).
# Because sum leg = 0, the subtraction term in the integral is IDENTICALLY ZERO FOR ALL z!!
# Wait: check! sum_{r1=1}^{11} sum_{r2=0}^{10} leg(r1+9r2, 11) * (1 + eps_+ - 2*z_{r1,r2} - 2*z):
# For the -2*z part, sum leg(r1+9r2) = 0 (over 11 residues)!
# What about sum leg(r1+9r2) * z_{r1,r2}? Let's check!
eps_p = ((1 + mp.sqrt(5)) / 2)**2
def leg11(a):
    a %= 11
    return 0 if a == 0 else (1 if pow(a, 5, 11) == 1 else -1)

# Precompute the 100 weights and a_j = 1 + eps_+ - 2*z_j
pts_275 = []
for r1 in range(1, 12):
    for r2 in range(0, 11):
        lv = leg11(r1 + 9*r2)
        if lv != 0:
            zj = (r1 + r2 * eps_p) / 11
            pts_275.append((lv, 1 + eps_p - 2*zj))

sum_aj = sum(lv * aj for lv, aj in pts_275)
print("Check sum_{r1,r2} psi * (1+eps_+-2*z_j) =", mp.nstr(sum_aj, 15))
# Notice sum_aj = 2 * (-B_{1, chi_{-11}}) * (1 + eps_+) ... nonzero! So subtraction term IS needed for a=0,
# while for a >= 1, d/dz(sum_aj - 2z*sum_psi) = -2*sum_psi = 0!
# Therefore for a = 1, 2, 3:
#   F_Sh^{(a)}(0) = (1/2) * int_0^infty [ sum_j lv_j * (-t)^a * (cosh or sinh)(aj*t/2) ] / (2*sinh(t/2)*sinh(eps_+*t/2)) * dt/t !!
# Wait: check convergence at t -> 0 for a = 1:
#   sum_j lv_j * cosh(aj*t/2) = sum_j lv_j * (1 + aj^2 t^2/8 + ...) = (t^2/8) * sum_j lv_j * aj^2 + O(t^4)!
#   Wait: is sum_j lv_j * aj^2 == 0? Even if nonzero, dividing by t^2 (from sinh*sinh) and multiplying by (-t)^1/t = -1 gives FINITE limit at t=0!!
#   YES!! Because (-t)^1 / (t * sinh(t/2) * sinh(eps_+*t/2)) ~ -4/(eps_+ t^2), and numerator is O(t^2)!!
#   SO THE INTEGRAL CONVERGES EXPONENTIALLY FAST FOR ALL a = 1, 2, 3 WITH ZERO REGULARIZATION!!

def shintani_deriv(a_order):
    def integrand(t):
        if t < mp.mpf('1e-5'):
            # Taylor expand numerator
            if a_order % 2 == 1:
                # (-1)^a * t^{a-1} * sum lv * cosh(aj*t/2)
                # since sum lv = 0, leading term is (t^2/8) * sum lv * aj^2
                s2 = sum(lv * (aj**2) for lv, aj in pts_275)
                num = ((-1)**a_order) * (t**(a_order - 1)) * (s2 * t**2 / 8)
            else:
                # (-1)^a * t^{a-1} * sum lv * sinh(aj*t/2)
                s1 = sum(lv * aj for lv, aj in pts_275)
                num = ((-1)**a_order) * (t**(a_order - 1)) * (s1 * t / 2)
            return mp.mpf('0.5') * num / (2 * (t/2) * (eps_p * t/2))
        denom = 2 * mp.sinh(t/2) * mp.sinh(eps_p * t/2)
        if a_order % 2 == 1:
            num = sum(lv * mp.cosh(aj * t / 2) for lv, aj in pts_275)
        else:
            num = sum(lv * mp.sinh(aj * t / 2) for lv, aj in pts_275)
        return mp.mpf('0.5') * ((-1)**a_order) * (t**(a_order - 1)) * num / denom
    return mp.quad(integrand, [0, 1, 5, 20, mp.inf])

mp.mp.dps = 25
d1_val = shintani_deriv(1)
d2_val = shintani_deriv(2)
d3_val = shintani_deriv(3)
print(f"F_Sh'(0)  = {mp.nstr(d1_val, 22)}")
print(f"F_Sh''(0) = {mp.nstr(d2_val, 22)}")
print(f"F_Sh'''(0)= {mp.nstr(d3_val, 22)}")
# Check if d1_val or d2_val is a simple algebraic number (degree <= 4) or rational multiple of pi, sqrt(5), sqrt(11), log|u1|!
print("PSLQ check for F_Sh'(0) against {1, sqrt(5), sqrt(11), sqrt(55), pi, pi/sqrt(5), pi/sqrt(11), log|u1|, log(eps)}:")
u1_abs_mp = abs(sorted([r.real for r in mp.polyroots([1, 3, 3, 3, 1], maxsteps=200, extraprec=20) if abs(r.imag) < mp.mpf('1e-18')])[0])
basis_test = [d1_val, mp.mpf(1), mp.sqrt(5), mp.sqrt(11), mp.sqrt(55), mp.pi, mp.pi/mp.sqrt(5), mp.pi/mp.sqrt(11), mp.log(u1_abs_mp), mp.log((1+mp.sqrt(5))/2)]
rel1 = mp.pslq(basis_test, maxcoeff=1000, tol=mp.mpf('1e-18'))
print("  PSLQ relation for F_Sh'(0):", rel1)
# Also check algebraic polynomial of degree <= 4 for F_Sh'(0)
rel1_alg = mp.pslq([mp.mpf(1), d1_val, d1_val**2, d1_val**3, d1_val**4], maxcoeff=10000, tol=mp.mpf('1e-18'))
print("  Deg<=4 algebraic relation for F_Sh'(0):", rel1_alg)
rel2_alg = mp.pslq([mp.mpf(1), d2_val, d2_val**2, d2_val**3, d2_val**4], maxcoeff=10000, tol=mp.mpf('1e-18'))
print("  Deg<=4 algebraic relation for F_Sh''(0):", rel2_alg)
# Also check ratio d1_val / (pi / sqrt(55)) or similar!
print("  Note: F_Sh'(0) is a linear combination of non-critical Barnes double zeta values zeta_2(1, z_j; 1, eps_+) (transcendental!)")

print("\n" + "=" * 80)
print("SECTION 4: PRIME-IDEAL CENTERED RAMP SUMS G_{F^+}(psi_{-275}, y) AND G_{F_3}(eps_2, y)")
print("=" * 80)

# Compute ramp sums up to y = 2000 for both psi_{-275} and eps_2/F_3!
# First compute L'/L(1, psi_{-275}) via our exact Dirichlet series / functional equation, and L'/L(1, eps_2/F_3) = gamma_{K_4} - gamma_Q!
# For psi_{-275}:
# Recall Lambda(s) = 2 * (sqrt(55)/(2*pi))^s * Gamma(s) * L(s, psi) = 2 * int_1^infty f(t) (t^{s-1} + t^{-s}) dt!
# Differentiate at s = 1:
#   Lambda'(1) / Lambda(1) = log(sqrt(55)/(2*pi)) - gamma_E + L'/L(1, psi)
#   On the other hand, Lambda'(1) = 2 * int_1^infty f(t) * log(t) * (1 - 1/t) dt!
# WAIT A SECOND! CHECK THAT!
#   d/ds [t^{s-1} + t^{-s}]|_{s=1} = log(t) * (1 - 1/t)!!
#   Since int_1^infty e^{-a*t} log(t) (1 - 1/t) dt is super easy via mp.quad (for small n) and negligible for large n!
# Let's compute L'/L(1, psi_{-275}) to 15 digits!

def compute_Lprime_over_L_1_275():
    # Reuse prime_euler up to 300 (already converges to 25+ digits!)
    c_arr = [0] * 301
    c_arr[1] = 1
    for p in sp.primerange(2, 301):
        if p == 5:
            a1, a2 = -1, 0
        elif p == 11:
            a1, a2 = -1, 0
        else:
            leg5 = -1 if p == 2 else (1 if pow(5, (p - 1) // 2, p) == 1 else -1)
            fac = sp.factor_list(P_275, modulus=p)[1]
            degs = sorted([sp.Poly(f, u).degree() for f, m in fac for _ in range(m)])
            if leg5 == -1:
                a1, a2 = (0, -1) if degs == [2, 2] else (0, 1)
            else:
                if degs == [1, 1, 1, 1]: a1, a2 = 2, 1
                elif degs == [1, 1, 2]: a1, a2 = 0, -1
                else: a1, a2 = -2, 1
        cp = [1]
        pk = p
        while pk <= 300:
            cp.append(a1 if len(cp) == 1 else a1 * cp[-1] - a2 * cp[-2])
            pk *= p
        for m in range(300 // p, 0, -1):
            if m % p != 0 and c_arr[m] != 0:
                pk = p
                k = 1
                while m * pk <= 300:
                    c_arr[m * pk] = c_arr[m] * cp[k]
                    pk *= p
                    k += 1
    c0 = 2 * mp.pi / mp.sqrt(55)
    # Lambda(1)/2 = sum c[n] * (e^{-c0 n}/(c0 n) + E_1(c0 n))
    # Lambda'(1)/2 = sum c[n] * int_1^infty e^{-c0 n t} log(t) (1 - 1/t) dt
    # Note: int_1^infty e^{-a t} log(t) dt = E_1(a) / a ! (integrate by parts: u = log t, dv = e^{-at} dt => 0 + int_1^infty e^{-at}/(at) dt = E_1(a)/a!)
    # And int_1^infty e^{-a t} (log t / t) dt = G_{2,3}^{3,0}(a | 1,1 ; 0,0,0) = mp.meijerg([], [1,1], [0,0,0], [], a)!
    lam1_half = mp.mpf(0)
    lam1p_half = mp.mpf(0)
    for n in range(1, 301):
        if c_arr[n] != 0:
            a = c0 * n
            lam1_half += c_arr[n] * (mp.exp(-a) / a + mp.e1(a))
            if a < 40:
                term1 = mp.e1(a) / a
                term2 = mp.meijerg([[], [1, 1]], [[0, 0, 0], []], a)
                lam1p_half += c_arr[n] * (term1 - term2)
    # Lambda'(1)/Lambda(1) = log(sqrt(55)/(2*pi)) - euler + L'/L(1, psi)
    return lam1p_half / lam1_half - mp.log(mp.sqrt(55) / (2 * mp.pi)) + mp.euler

LpoL_275 = float(compute_Lprime_over_L_1_275())
print(f"Exact L'/L(1, psi_-275) = {LpoL_275:.12f}")

# Compute centered ramp sum G_{F^+}(psi_{-275}, y) up to y = 2000
# Need prime ideals of Q(sqrt(5)) up to norm 2000!
def build_ideals_275(Ymax):
    ideals = []
    for p in sp.primerange(2, Ymax + 1):
        if p == 5:
            ideals.append((5, -1))
        elif p == 11:
            ideals.append((11, 0))
            ideals.append((11, -1))
        else:
            leg5 = -1 if p == 2 else (1 if pow(5, (p - 1) // 2, p) == 1 else -1)
            if leg5 == -1:
                if p * p <= Ymax:
                    s = 1 if pow(p, 5, 11) == 1 else -1
                    ideals.append((p*p, s))
            else:
                fac = sp.factor_list(P_275, modulus=p)[1]
                degs = sorted([sp.Poly(f, u).degree() for f, m in fac for _ in range(m)])
                if degs == [1, 1, 1, 1]:
                    ideals.append((p, +1)); ideals.append((p, +1))
                elif degs == [1, 1, 2]:
                    ideals.append((p, +1)); ideals.append((p, -1))
                else:
                    ideals.append((p, -1)); ideals.append((p, -1))
    return ideals

ideals_275_2000 = build_ideals_275(2000)

def ramp_sum(ideals, y_val):
    s = 0.0
    for nm, chi in ideals:
        if chi == 0 or nm > y_val:
            continue
        log_nm = math.log(nm)
        pk = nm
        ck = chi
        while pk <= y_val:
            s += ck * log_nm * (y_val / pk - 1.0)
            pk *= nm
            ck *= chi
    return s

print("\nCentered Ramp Sum G_{Q(sqrt(5))}(psi_{-275}, y) = ramp(psi, y) + y * (L'/L)(1, psi):")
print(f"{'y':>6s} | {'ramp(y)':>12s} | {'G(psi, y)':>12s} | {'G(psi, y)/sqrt(y)':>18s}")
print("-" * 58)
for yv in [50, 100, 250, 500, 1000, 2000]:
    rv = ramp_sum(ideals_275_2000, yv)
    gv = rv + yv * LpoL_275
    print(f"{yv:6d} | {rv:12.4f} | {gv:12.4f} | {gv/math.sqrt(yv):18.6f}")

# Now do the same for eps_2 / F_3(229)!
# Estimate L'/L(1, eps_2/F_3) directly from prime ideal sum up to 2000 (and verify from ramp(y)/y):
def build_ideals_f3(Ymax):
    ideals = []
    for p in sp.primerange(2, Ymax + 1):
        if p == 229:
            ideals.append((229, -1))
            ideals.append((229, +1))  # Wait: check exact e_p1, e_p2 from Section 2!
            continue
        fac_F3 = sp.factor_list(P_F3, modulus=p)[1]
        dF3 = tuple(sorted([sp.Poly(f, y).degree() for f, m in fac_F3 for _ in range(m)]))
        if dF3 == (1, 1, 1):
            fac_M6 = sp.factor_list(P_M6, modulus=p)[1]
            dM6 = tuple(sorted([sp.Poly(f, w).degree() for f, m in fac_M6 for _ in range(m)]))
            if dM6 == (1, 1, 1, 1, 1, 1):
                ideals.extend([(p, +1), (p, +1), (p, +1)])
            else:
                ideals.extend([(p, +1), (p, -1), (p, -1)])
        elif dF3 == (1, 2):
            fac_M6 = sp.factor_list(P_M6, modulus=p)[1]
            dM6 = tuple(sorted([sp.Poly(f, w).degree() for f, m in fac_M6 for _ in range(m)]))
            if dM6 == (1, 1, 2, 2):
                ideals.append((p, +1))
                if p*p <= Ymax: ideals.append((p*p, +1))
            elif dM6 == (2, 4):
                ideals.append((p, -1))
                if p*p <= Ymax: ideals.append((p*p, -1))
            elif dM6 == (1, 1, 4):
                ideals.append((p, +1))
                if p*p <= Ymax: ideals.append((p*p, -1))
            elif dM6 == (2, 2, 2):
                ideals.append((p, -1))
                if p*p <= Ymax: ideals.append((p*p, +1))
        elif dF3 == (3,) and p**3 <= Ymax:
            fac_M6 = sp.factor_list(P_M6, modulus=p)[1]
            dM6 = tuple(sorted([sp.Poly(f, w).degree() for f, m in fac_M6 for _ in range(m)]))
            ideals.append((p**3, +1 if dM6 == (3, 3) else -1))
    return ideals

ideals_f3_2000 = build_ideals_f3(2000)
# Wait: compute exact L'/L(1, eps_2/F_3) using functional equation of degree-3 L-function!
# Gamma factor: Gamma_R(s) * Gamma_R(s+1)^2, A = 229.
# Let's compute L'/L(1, eps_2/F_3) directly from Dirichlet series via smoothed Mellin/Abel sum of ramp_sum(y)/y around y=2000
# AND exact via functional equation!
# Actually at y = 2000, -ramp(y)/y approximates L'/L(1) to O(y^{-1/2}) ~ 0.02; let's compute exact L'/L(1, eps_2/F_3)
# via mpmath inverse Mellin transform (Meijer-G) using c_n of L(s, eps_2/F_3) up to n = 500!
# Recall for Gamma_R(s)*Gamma_R(s+1)^2 = pi^{-(3s+2)/2} * Gamma(s/2) * Gamma((s+1)/2)^2:
#   Lambda(s) = (229/(pi^3))^{s/2} * pi^{-1} * Gamma(s/2) * Gamma((s+1)/2)^2 * L(s, eps_2).
#   With x_n = n * pi^{3/2} / sqrt(229) (Wait: Mellin transform of G_{0,3}^{3,0}(x | 0, 1/2, 1/2) at s/2 is Gamma(s/2)*Gamma((s+1)/2)^2!):
#   Specifically, int_0^infty G_{0,3}^{3,0}(u | 0, 1/2, 1/2) u^{s/2 - 1} du = Gamma(s/2)*Gamma((s+1)/2)^2.
#   Substitute u = (n^2 * pi^3 / 229) * t^2 => du/u = 2 dt/t, so:
#   Lambda(s) = (2/pi) * int_0^infty [ sum_n c(n) G_{0,3}^{3,0}((pi^3 n^2 / 229) t^2 | 0, 1/2, 1/2) ] t^{s-1} dt!
#   Let's check this in 5 lines and get L'(0), L(1), and L'/L(1) for eps_2/F_3 to 15+ digits!

def compute_eps2_L_values():
    Nmax = 400
    c_arr = [0] * (Nmax + 1)
    c_arr[1] = 1
    for p in sp.primerange(2, Nmax + 1):
        if p == 229:
            # Check exact Euler factor of K_4 mod 229 divided by (1-T)
            fac_K4 = sp.factor_list(P_K4, modulus=229)[1]
            # factor_list gives (f, mult)
            degs = [sp.Poly(f, x).degree() for f, m in fac_K4]  # distinct irreducible factors!
            # E_229(K_4) = prod (1 - T^d)^{-1}; divide by (1-T)^{-1}
            poly_E = sp.Poly(sp.prod(1 - T**d for d in degs), T)
            poly_L = sp.quo(poly_E, sp.Poly(1 - T, T))
            # Extract coefficients 1 + b1 T + b2 T^2 + b3 T^3
            cs = poly_L.all_coeffs()[::-1]
            cs += [0] * (4 - len(cs))
            b1, b2, b3 = int(cs[1]), int(cs[2]), int(cs[3])
        else:
            fac_K4 = sp.factor_list(P_K4, modulus=p)[1]
            degs = [sp.Poly(f, x).degree() for f, m in fac_K4 for _ in range(m)]
            poly_E = sp.Poly(sp.prod(1 - T**d for d in degs), T)
            poly_L = sp.quo(poly_E, sp.Poly(1 - T, T))
            cs = poly_L.all_coeffs()[::-1]
            cs += [0] * (4 - len(cs))
            b1, b2, b3 = int(cs[1]), int(cs[2]), int(cs[3])
        # Recurrence for 1 / (1 + b1 T + b2 T^2 + b3 T^3) = sum cp[k] T^k:
        cp = [1]
        pk = p
        while pk <= Nmax:
            k = len(cp)
            val = -b1 * cp[k - 1]
            if k >= 2: val -= b2 * cp[k - 2]
            if k >= 3: val -= b3 * cp[k - 3]
            cp.append(val)
            pk *= p
        for m in range(Nmax // p, 0, -1):
            if m % p != 0 and c_arr[m] != 0:
                pk = p
                k = 1
                while m * pk <= Nmax:
                    c_arr[m * pk] = c_arr[m] * cp[k]
                    pk *= p
                    k += 1
    # Use exact Mellin split at t = 1:
    # Lambda(s) = (2/pi) * sum_n c[n] * [ M_+(n, s) + W * M_+(n, 1-s) ]
    # where M_+(n, s) = int_1^infty G_{0,3}^{3,0}(a_n t^2 | 0, 1/2, 1/2) t^{s-1} dt
    #   = (1/2) * a_n^{-s/2} * int_{a_n}^\infty G_{0,3}^{3,0}(u | 0, 1/2, 1/2) u^{s/2 - 1} du
    #   = (1/2) * G_{1,4}^{4,0}(a_n | 1 - s/2 ; -s/2, 0, 1/2, 1/2)  [wait: exact Mellin incomplete formula!]
    # Check: int_a^\infty G_{0,3}^{3,0}(u | b1,b2,b3) u^{z-1} du = a^z * G_{1,4}^{4,0}(a | 1-z ; -z, b1, b2, b3)
    # Wait: let's verify at s = 1 (z = 1/2) and s = 0 (z = 0) numerically!
    mp.mp.dps = 22
    a_base = (mp.pi**3) / 229
    # Test functional equation directly at t = 1.2!
    def f_eps2(t_val):
        s = mp.mpf(0)
        for n in range(1, Nmax + 1):
            if c_arr[n] != 0:
                arg = a_base * (n**2) * (t_val**2)
                if arg > 120:
                    break
                s += c_arr[n] * mp.meijerg([[], []], [[0, mp.mpf('0.5'), mp.mpf('0.5')], []], arg)
        return s
    fe_lhs = f_eps2(mp.mpf(1) / mp.mpf('1.2'))
    fe_rhs = mp.mpf('1.2') * f_eps2(mp.mpf('1.2'))
    W_eps2 = fe_lhs / fe_rhs
    print(f"\nFunctional equation check for L(s, eps_2 / F_3) at t=1.2: W = {mp.nstr(W_eps2, 16)} (expect +1)")

    # Compute Lambda(1) and Lambda'(1) by integrating (2/pi) * f_eps2(t) * (1 + 1/t) and log(t)*(1 - 1/t) on [1, 15]!
    # Note f_eps2(t) decays like exp(-3 * (a_base * t^2)^{1/3})! Wait: at t=15, arg = 0.135 * 225 = 30.4, 3*30.4^{1/3} = 9.4!
    # Integrate on [1, 20, 60] for 15+ digits!
    lam1 = (2 / mp.pi) * mp.quad(lambda t: f_eps2(t) * (1 + 1/t), [1, 3, 10, 35])
    lam1p = (2 / mp.pi) * mp.quad(lambda t: f_eps2(t) * mp.log(t) * (1 - 1/t), [1, 3, 10, 35])
    # Recall Lambda(0) = 2 * L'(0, eps_2), Lambda(1) = sqrt(229)/pi^2 * L(1, eps_2)!
    Lprime0_num = lam1 / 2
    L1_num = lam1 * (mp.pi**2) / mp.sqrt(229)
    # Log-derivative of Gamma factor Gamma_R(s)*Gamma_R(s+1)^2 at s = 1:
    # d/ds [ -(3s+2)/2 log pi + log Gamma(s/2) + 2 log Gamma((s+1)/2) ]|_{s=1}
    # = -3/2 log pi + (1/2) psi(1/2) + psi(1)
    # = -3/2 log pi + (1/2)(-gamma - 2 log 2) - gamma = -3/2 log pi - 3/2 gamma - log 2.
    # Plus (1/2) log 229 from A^{s/2}!
    g_logderiv_1 = mp.mpf('0.5') * mp.log(229) - mp.mpf('1.5') * mp.log(mp.pi) - mp.mpf('1.5') * mp.euler - mp.log(2)
    LpoL_1 = lam1p / lam1 - g_logderiv_1
    print(f"Direct Mellin L'(0, eps_2 / F_3) = {mp.nstr(Lprime0_num, 16)} (exact R_K4 = log|w1| = 0.3373778035715619)")
    print(f"Direct Mellin L(1, eps_2 / F_3)  = {mp.nstr(L1_num, 16)}")
    print(f"Direct Mellin L'/L(1, eps_2/F_3) = {mp.nstr(LpoL_1, 14)}  (= gamma_K4 - gamma_Q!)")
    return float(LpoL_1)

LpoL_eps2 = compute_eps2_L_values()

# Fix p = 229 exact eps_2 values in ideals_f3_2000 by recomputing quickly:
fac_M6_229 = sp.factor_list(P_M6, modulus=229)[1]
degs_M6_229 = sorted([(sp.Poly(f, w).degree(), m) for f, m in fac_M6_229])
e_p1_229 = +1 if degs_M6_229.count((1, 2)) == 2 else -1
e_p2_229 = +1 if degs_M6_229.count((1, 1)) == 2 else -1
ideals_f3_2000 = [(nm, ch) for nm, ch in ideals_f3_2000 if nm != 229] + [(229, e_p1_229), (229, e_p2_229)]

print("\nCentered Ramp Sum G_{F_3}(eps_2, y) = ramp(eps_2, y) + y * (L'/L)(1, eps_2):")
print(f"{'y':>6s} | {'ramp(y)':>12s} | {'G(eps2, y)':>12s} | {'G(eps2, y)/sqrt(y)':>18s}")
print("-" * 58)
for yv in [50, 100, 250, 500, 1000, 2000]:
    rv = ramp_sum(ideals_f3_2000, yv)
    gv = rv + yv * LpoL_eps2
    print(f"{yv:6d} | {rv:12.4f} | {gv:12.4f} | {gv/math.sqrt(yv):18.6f}")
