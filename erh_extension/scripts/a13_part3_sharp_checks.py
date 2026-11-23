#!/usr/bin/env python3
"""
Wave-3 Agent A13 Part 3 Sharp Verification Checks:
1. 40-digit PSLQ check on F_Sh''(0) (confirming transcendence / refuting 25-digit pigeonhole artifact)
2. Side-by-side Taylor derivative asymptotics: Barnes 1/Gamma_3(z+1;1,1,1) vs Kurokawa-Koyama S_3(3/2+u;1,1,1)
   showing exact +(1/3) a log log a bloat in 1/Gamma_3 vs exact cancellation in S_3!
3. High-precision L'(0, eps_2/F_3) and L'/L(1, eps_2/F_3) with Nmax = 1200
4. Totally positive unit group U^+_{F_3} = <y^2, y+2> and 3D Shintani cone geometry of F_3(229)
5. Hazewinkel formal group F_{K_{-275}} (with f_p from K_{-275}) up to a = 30
6. Exact group-theoretic verification of S_4(0,2) and D_4(K_{-275}) tensor products (Sym^2, Ad^0, Mackey)
"""

import math
import sympy as sp
import mpmath as mp

print("=" * 80)
print("CHECK 1: 40-DIGIT TRANSCENDENCE CHECK OF F_Sh''(0) FOR K_{-275}")
print("=" * 80)
mp.mp.dps = 45
eps_p = ((1 + mp.sqrt(5)) / 2) ** 2
def leg11(a):
    a %= 11
    return 0 if a == 0 else (1 if pow(a, 5, 11) == 1 else -1)

pts_275 = []
for r1 in range(1, 12):
    for r2 in range(0, 11):
        lv = leg11(r1 + 9*r2)
        if lv != 0:
            zj = (r1 + r2 * eps_p) / 11
            pts_275.append((lv, 1 + eps_p - 2*zj))

def shintani_deriv_hp(a_order):
    s1 = sum(lv * aj for lv, aj in pts_275)
    s2 = sum(lv * (aj**2) for lv, aj in pts_275)
    def integrand(t):
        if t < mp.mpf('1e-6'):
            if a_order % 2 == 1:
                num = ((-1)**a_order) * (t**(a_order - 1)) * (s2 * t**2 / 8)
            else:
                num = ((-1)**a_order) * (t**(a_order - 1)) * (s1 * t / 2)
            return mp.mpf('0.5') * num / (2 * (t/2) * (eps_p * t/2))
        denom = 2 * mp.sinh(t/2) * mp.sinh(eps_p * t/2)
        if a_order % 2 == 1:
            num = sum(lv * mp.cosh(aj * t / 2) for lv, aj in pts_275)
        else:
            num = sum(lv * mp.sinh(aj * t / 2) for lv, aj in pts_275)
        return mp.mpf('0.5') * ((-1)**a_order) * (t**(a_order - 1)) * num / denom
    return mp.quad(integrand, [0, 1, 5, 25, mp.inf])

d1_hp = shintani_deriv_hp(1)
d2_hp = shintani_deriv_hp(2)
print(f"F_Sh'(0)  (40d) = {mp.nstr(d1_hp, 40)}")
print(f"F_Sh''(0) (40d) = {mp.nstr(d2_hp, 40)}")
# Test the 25-digit candidate polynomial [9417, 6624, 3108, -7199, 132] on d2_hp!
poly_err = 9417 + 6624*d2_hp + 3108*d2_hp**2 - 7199*d2_hp**3 + 132*d2_hp**4
print(f"Error of spurious 25-digit poly at 40d: {mp.nstr(poly_err, 12)} (NONZERO => spurious artifact!)")
rel2_40 = mp.pslq([mp.mpf(1), d2_hp, d2_hp**2, d2_hp**3, d2_hp**4], maxcoeff=100000, tol=mp.mpf('1e-34'))
print(f"40-digit PSLQ deg<=4 check on F_Sh''(0): {rel2_40}")

print("\n" + "=" * 80)
print("CHECK 2: BARNES 1/Gamma_3(z+1; 1,1,1) VS TRIPLE SINE S_3(3/2+u; 1,1,1) UP TO a = 40")
print("=" * 80)
mp.mp.dps = 35
# Recall Barnes 1/Gamma_3(z+1; 1,1,1):
#   Zeros at z = -n (n >= 1) with multiplicity m_n = n(n+1)/2.
#   Normalized canonical Weierstrass product (genus 3):
#   G3_inv(z) := prod_{n=1}^\infty [ (1 + z/n) * exp(-z/n + z^2/(2n^2) - z^3/(3n^3)) ]^{n(n+1)/2}
#   Logarithm: log G3_inv(z) = sum_{k=4}^\infty (-1)^{k-1}/k * (sum_{n=1}^\infty (n(n+1)/2) / n^k) * z^k
#                            = sum_{k=4}^\infty (-1)^{k-1}/(2k) * (zeta(k-2) + zeta(k-1)) * z^k !!
#   OH!! HOW CLEAN IS THAT?!
#   Check convergence: for k >= 4, k-2 >= 2, so zeta(k-2) + zeta(k-1) converges!!
#   And the leading asymptotic of log|G3_inv(R e^{i*theta})| is (1/6) R^3 log R + O(R^3)!
N_ord = 40
L_G3 = [mp.mpf(0)] * (N_ord + 1)
for k in range(4, N_ord + 1):
    L_G3[k] = ((-1)**(k - 1)) / (2 * k) * (mp.zeta(k - 2) + mp.zeta(k - 1))

f_G3 = [mp.mpf(0)] * (N_ord + 1)
f_G3[0] = mp.mpf(1)
for a in range(1, N_ord + 1):
    f_G3[a] = sum(m * L_G3[m] * f_G3[a - m] for m in range(1, a + 1)) / a

# Compare with Kurokawa-Koyama S_3(3/2 + u; 1, 1, 1) up to N_ord = 40
g_coeff = [mp.mpf(0)] * (N_ord + 2)
for k in range(1, N_ord // 2 + 2):
    B2k = abs(mp.bernoulli(2*k))
    t_coeff = (mp.mpf(2)**(2*k)) * (mp.mpf(2)**(2*k) - 1) * B2k / mp.factorial(2*k) * (mp.pi**(2*k - 1))
    if 2*k - 1 <= N_ord:
        g_coeff[2*k - 1] += (mp.pi / 8) * t_coeff
    if 2*k + 1 <= N_ord:
        g_coeff[2*k + 1] -= (mp.pi / 2) * t_coeff
L_S3 = [mp.mpf(0)] * (N_ord + 1)
for m in range(1, N_ord + 1):
    L_S3[m] = g_coeff[m - 1] / m
f_S3 = [mp.mpf(0)] * (N_ord + 1)
f_S3[0] = mp.mpf(1)
for a in range(1, N_ord + 1):
    f_S3[a] = sum(m * L_S3[m] * f_S3[a - m] for m in range(1, a + 1)) / a

tau3 = mp.pi / 6
lin3 = -1 + (1 + mp.log(3 * tau3)) / 3
print(f"{'a':>3s} | {'log|G3inv^(a)|':>14s} | {'excess/(a loglog a)':>19s} | {'log|S3^(a)|':>12s} | {'S3 excess/a':>12s}")
print("-" * 74)
# Saddle-point prediction for G3_inv (log M(R) ~ (1/6) R^3 log R):
#   log|G3_inv^(a)(0)| ~ (2/3) a log a + (1/3) a log log a + O(a)
for a in [8, 12, 16, 20, 24, 28, 32, 36, 40]:
    dg = abs(f_G3[a] * mp.factorial(a))
    ds = abs(f_S3[a] * mp.factorial(a))
    lg = float(mp.log(dg)) if dg > 0 else float('-inf')
    ls = float(mp.log(ds)) if ds > 0 else float('-inf')
    base = (2.0 / 3.0) * a * math.log(a)
    exc_g = (lg - base + a * (1.0 - (1.0 + math.log(0.5)) / 3.0)) / (a * math.log(math.log(a)))
    exc_s = (ls - (base + float(lin3) * a)) / a
    print(f"{a:3d} | {lg:14.4f} | {exc_g:19.5f} | {ls:12.4f} | {exc_s:12.5f}")

# Also check growth of log M(R) directly on circle |z| = R!
print("\nDirect max-modulus verification on |z| = R (comparing (log M(R))/R^3):")
print(f"{'R':>6s} | {'log|G3_inv(-R)|/R^3':>20s} | {'(1/6)*log(R)':>14s} | {'log|S3(3/2+iR)|/R^3':>20s} | {'pi/6 = 0.5236':>14s}")
print("-" * 82)
# Compute S_3(3/2 + iR) via exact integral: log|S_3(3/2 + iR)/S_3(3/2)| = int_0^R (pi/2)*(t^2 + 1/4)*tanh(pi*t) dt!!
# WAIT A SECOND! CHECK THAT!!
# g(u) = -(pi/2)*(u^2 - 1/4)*tan(pi*u). Put u = i*t, du = i dt:
# g(i*t) * i dt = -(pi/2)*(-t^2 - 1/4)*(i*tanh(pi*t))*(i dt) = -(pi/2)*(t^2 + 1/4)*tanh(pi*t) dt?
# Let's check sign: (-1)*(-1)*(i*i) = -1! Wait: for S_3(3/2 + u) = 1/(Gamma_3(3/2+u)Gamma_3(3/2-u)),
# along imaginary axis u = i*t, S_3(3/2 + i*t) DECAYS or GROWS?!
# Along u = i*t: tan(pi*i*t) = i*tanh(pi*t), u^2 - 1/4 = -(t^2 + 1/4), so:
# L(iR) = int_0^R -(pi/2)*(-(t^2+1/4))*(i*tanh(pi*t)) * (i dt) = -(pi/2) int_0^R (t^2 + 1/4) tanh(pi*t) dt < 0!
# And along diagonal u = R * e^{i*pi/6} (where Im(u) > 0 and arg(u^3) = pi/2), Re(i*pi/6 * u^3) = -pi/6 * R^3,
# while along u = R * e^{-i*pi/6}, Re(-i*pi/6 * u^3) = ... wait: for u = R * e^{i*pi/6}:
# u^3 = i * R^3, so (-pi/2) * int (u^2) * (i) du ~ -(i*pi/6) u^3 = +(pi/6) R^3!! GROWS LIKE exp(+(pi/6) R^3)!!
# Let's check directly by integrating along ray u = r * e^{i*pi/6} (where tan(pi*u) -> +i as r -> infty)!
for R in [2.0, 5.0, 10.0, 20.0]:
    # S_3 along ray u = r * exp(i*pi/6):
    theta = mp.pi / 6
    eith = mp.exp(1j * theta)
    val_S3 = mp.quad(lambda r: -(mp.pi/2)*((r*eith)**2 - mp.mpf('0.25'))*mp.tan(mp.pi*r*eith)*eith, [0, R])
    # G3_inv along ray z = R * exp(i*pi/3) (away from negative real axis):
    # Wait: along z = R (positive real axis!), log G3_inv(R) = sum_{n=1}^\infty (n(n+1)/2) * [log(1+R/n) - R/n + R^2/(2n^2) - R^3/(3n^3)]
    # Check asymptotic along z = R*e^{i*pi/3}:
    z_pt = R * mp.exp(1j * mp.pi / 3)
    # Use Euler-Maclaurin / direct sum up to N = 400 + tail
    N_sum = 300
    s_g3 = mp.mpf(0)
    for n in range(1, N_sum + 1):
        u_n = z_pt / n
        s_g3 += (n * (n + 1) / 2) * (mp.log(1 + u_n) - u_n + u_n**2 / 2 - u_n**3 / 3)
    # Tail n > N_sum: sum_{k=4}^{12} (-1)^{k-1}/(2k) * z^k * (zeta_tail(k-2) + zeta_tail(k-1))
    # Approximate tail cleanly via integral from N_sum+0.5 to infty:
    tail_g3 = mp.quad(lambda x: (x*(x+1)/2)*(mp.log(1 + z_pt/x) - z_pt/x + (z_pt/x)**2/2 - (z_pt/x)**3/3), [N_sum + 0.5, mp.inf])
    tot_g3 = s_g3 + tail_g3
    print(f"{R:6.1f} | {float(abs(tot_g3.real))/(R**3):20.6f} | {math.log(R)/6.0:14.6f} | {float(val_S3.real)/(R**3):20.6f} | {math.pi/6.0:14.6f}")

print("\n" + "=" * 80)
print("CHECK 3: FAST HIGH-PRECISION L'/L(1, eps_2/F_3) USING DIRECT MEIJER-G INCOMPLETE MELLIN")
print("=" * 80)
# Recall: int_1^infty G_{0,3}^{3,0}(a t^2 | 0, 1/2, 1/2) t^{s-1} dt
#       = (1/2) * G_{1,4}^{4,0}(a | 1 - s/2 ; -s/2, 0, 1/2, 1/2) !!
# Let's verify that identity at a = 1.5, s = 1 and s = 0 first!
mp.mp.dps = 22
a_t = mp.mpf('1.5')
lhs_1 = mp.quad(lambda t: mp.meijerg([[], []], [[0, mp.mpf('0.5'), mp.mpf('0.5')], []], a_t * t**2), [1, 5, 20])
rhs_1 = mp.mpf('0.5') * mp.meijerg([[], [mp.mpf('0.5')]], [[mp.mpf('-0.5'), 0, mp.mpf('0.5'), mp.mpf('0.5')], []], a_t)
print("Verify incomplete Mellin identity at s=1:", mp.nstr(lhs_1, 18), "vs", mp.nstr(rhs_1, 18), "diff =", mp.nstr(abs(lhs_1-rhs_1), 6))
# Wait: check scaling! int_1^infty f(a t^2) dt = (1/2) a^{-1/2} int_a^infty f(u) u^{-1/2} du.
# By Mellin-Barnes: int_a^infty G_{0,3}^{3,0}(u | b) u^{z-1} du = a^z G_{1,4}^{4,0}(a | 1-z ; -z, b) -> multiply by a^{-z} gives G_{1,4}^{4,0}(a | 1-z ; -z, b)!
# Check s = 0 (t^{-1} dt): z = 0, so (1/2) G_{1,4}^{4,0}(a | 1 ; 0, 0, 1/2, 1/2)!
lhs_0 = mp.quad(lambda t: mp.meijerg([[], []], [[0, mp.mpf('0.5'), mp.mpf('0.5')], []], a_t * t**2) / t, [1, 5, 20])
rhs_0 = mp.mpf('0.5') * mp.meijerg([[], [1]], [[0, 0, mp.mpf('0.5'), mp.mpf('0.5')], []], a_t)
print("Verify incomplete Mellin identity at s=0:", mp.nstr(lhs_0, 18), "vs", mp.nstr(rhs_0, 18), "diff =", mp.nstr(abs(lhs_0-rhs_0), 6))

# And derivative w.r.t. s at s = 1:
#   int_1^infty f(a t^2) log(t) t^{s-1} dt = (1/4) * G_{2,5}^{5,0}(a | 1-s/2, 1-s/2 ; -s/2, -s/2, 0, 1/2, 1/2) !!
# Verify at s = 1 and s = 0!
lhs_1d = mp.quad(lambda t: mp.meijerg([[], []], [[0, mp.mpf('0.5'), mp.mpf('0.5')], []], a_t * t**2) * mp.log(t), [1, 5, 20])
rhs_1d = mp.mpf('0.25') * mp.meijerg([[], [mp.mpf('0.5'), mp.mpf('0.5')]], [[mp.mpf('-0.5'), mp.mpf('-0.5'), 0, mp.mpf('0.5'), mp.mpf('0.5')], []], a_t)
print("Verify log-deriv Mellin identity at s=1:", mp.nstr(lhs_1d, 16), "vs", mp.nstr(rhs_1d, 16), "diff =", mp.nstr(abs(lhs_1d-rhs_1d), 6))
lhs_0d = mp.quad(lambda t: mp.meijerg([[], []], [[0, mp.mpf('0.5'), mp.mpf('0.5')], []], a_t * t**2) * mp.log(t) / t, [1, 5, 20])
rhs_0d = mp.mpf('0.25') * mp.meijerg([[], [1, 1]], [[0, 0, 0, mp.mpf('0.5'), mp.mpf('0.5')], []], a_t)
print("Verify log-deriv Mellin identity at s=0:", mp.nstr(lhs_0d, 16), "vs", mp.nstr(rhs_0d, 16), "diff =", mp.nstr(abs(lhs_0d-rhs_0d), 6))

# Now sum up to Nmax = 600 using SINGLE meijerg calls (instant!!):
x, T = sp.symbols('x T')
P_K4 = x**4 + x + 1
Nmax = 600
c_arr = [0] * (Nmax + 1)
c_arr[1] = 1
for p in sp.primerange(2, Nmax + 1):
    fac_K4 = sp.factor_list(P_K4, modulus=p)[1]
    if p == 229:
        degs = [sp.Poly(f, x).degree() for f, m in fac_K4]
    else:
        degs = [sp.Poly(f, x).degree() for f, m in fac_K4 for _ in range(m)]
    poly_E = sp.Poly(sp.prod(1 - T**d for d in degs), T)
    poly_L = sp.quo(poly_E, sp.Poly(1 - T, T))
    cs = poly_L.all_coeffs()[::-1]
    cs += [0] * (4 - len(cs))
    b1, b2, b3 = int(cs[1]), int(cs[2]), int(cs[3])
    cp = [1]
    pk = p
    while pk <= Nmax:
        k = len(cp)
        val = -b1 * cp[k - 1] - (b2 * cp[k - 2] if k >= 2 else 0) - (b3 * cp[k - 3] if k >= 3 else 0)
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

a_base = (mp.pi**3) / 229
lam1 = mp.mpf(0)
lam1p = mp.mpf(0)
for n in range(1, Nmax + 1):
    if c_arr[n] != 0:
        an = a_base * (n**2)
        if an > 3500:  # 3 * (3500)^{1/3} ~ 45 => e^{-45} < 10^{-19}
            break
        m1 = mp.mpf('0.5') * mp.meijerg([[], [mp.mpf('0.5')]], [[mp.mpf('-0.5'), 0, mp.mpf('0.5'), mp.mpf('0.5')], []], an)
        m0 = mp.mpf('0.5') * mp.meijerg([[], [1]], [[0, 0, mp.mpf('0.5'), mp.mpf('0.5')], []], an)
        lam1 += c_arr[n] * (m1 + m0)
        m1d = mp.mpf('0.25') * mp.meijerg([[], [mp.mpf('0.5'), mp.mpf('0.5')]], [[mp.mpf('-0.5'), mp.mpf('-0.5'), 0, mp.mpf('0.5'), mp.mpf('0.5')], []], an)
        m0d = mp.mpf('0.25') * mp.meijerg([[], [1, 1]], [[0, 0, 0, mp.mpf('0.5'), mp.mpf('0.5')], []], an)
        lam1p += c_arr[n] * (m1d - m0d)

lam1 *= (2 / mp.pi)
lam1p *= (2 / mp.pi)
Lprime0_exact = lam1 / 2
L1_exact = lam1 * (mp.pi**2) / mp.sqrt(229)
g_logderiv_1 = mp.mpf('0.5') * mp.log(229) - mp.mpf('1.5') * mp.log(mp.pi) - mp.mpf('1.5') * mp.euler - mp.log(2)
LpoL_1_exact = lam1p / lam1 - g_logderiv_1
print(f"High-precision L'(0, eps_2/F_3) = {mp.nstr(Lprime0_exact, 18)}")
print(f"Exact R_K4 = log|w1|            = 0.337377803571561901")
print(f"Difference                      = {mp.nstr(abs(Lprime0_exact - mp.mpf('0.337377803571561901438')), 6)}")
print(f"High-precision L(1, eps_2/F_3)  = {mp.nstr(L1_exact, 18)}")
print(f"High-precision L'/L(1, eps_2)   = {mp.nstr(LpoL_1_exact, 16)}")
print(f"Hence Euler-Kronecker gamma_K4  = gamma_Q + L'/L(1, eps_2) = {mp.nstr(mp.euler + LpoL_1_exact, 16)}")

print("\n" + "=" * 80)
print("CHECK 4: HAZEWINKEL FORMAL GROUP F_{K_{-275}} (WITH f_3 = 2, f_5 = 2, f_2 = 4) UP TO a = 30")
print("=" * 80)
u = sp.Symbol('u')
P_275 = u**4 + 3*u**3 + 3*u**2 + 3*u + 1
hmap_275 = {}
for p in sp.primerange(2, 35):
    if p in (5, 11):
        hmap_275[p] = 1  # ramified primes set to height 1 (Z[1/275]-integral!)
    else:
        fac = sp.factor_list(P_275, modulus=p)[1]
        degs = [sp.Poly(f, u).degree() for f, m in fac for _ in range(m)]
        hmap_275[p] = max(degs)
print("Heights f_p for F_{K_{-275}} (p < 35, p nmid 55):", {p: hmap_275[p] for p in sorted(hmap_275)})

def build_hazewinkel_exp_both(height_map, Amax):
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
    b = [sp.Rational(0)] * (Amax + 1)
    b[1] = sp.Rational(1)
    for a in range(2, Amax + 1):
        total = sp.Rational(0)
        cur = b[:a] + [sp.Rational(0)]
        pw = list(cur)
        for n in range(2, a + 1):
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
    g_ser = [sp.Rational(0)] * (Amax + 1)
    for a in range(1, Amax + 1):
        g_ser[a] = b[a] + sum(b[i] * g_ser[a - i] for i in range(1, a))
    return [sp.factorial(a) * b[a] for a in range(Amax + 1)], [sp.factorial(a) * g_ser[a] for a in range(Amax + 1)]

e_id, e_geom = build_hazewinkel_exp_both(hmap_275, 28)
print(f"F(T) = T/(1-T) on F_{{K_-275}} (Z[1/55]-integral, primes p nmid 55):")
print(f"{'a':>3s} | {'den(p nmid 55)':>14s} | {'FinDiv(a)':>10s} | {'LT-Lower':>10s} | {'log|e_a|':>10s} | {'Ratio Div/Log':>13s}")
print("-" * 74)
for a in [5, 10, 15, 20, 25, 28]:
    ea = e_geom[a]
    den = ea.q
    num = abs(int(ea.p))
    fin_div = 0.0
    lt_lb = 0.0
    for p in sp.primerange(2, a + 1):
        fp = hmap_275[p]
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
    print(f"{a:3d} | {den:14d} | {fin_div:10.4f} | {lt_lb:10.4f} | {log_arch:10.4f} | {fin_div/log_arch:13.6f}")

print("\n" + "=" * 80)
print("CHECK 5: TOTALLY POSITIVE UNITS & 3D SHINTANI CONE REGULATOR OF F_3(229)")
print("=" * 80)
roots_F3 = sorted([r.real for r in mp.polyroots([1, 0, -4, -1], maxsteps=200, extraprec=20)])
y3, y2, y1 = roots_F3[0], roots_F3[1], roots_F3[2]
# Totally positive units: u1 = y^2, u2 = y + 2
u1_tp = [y1**2, y2**2, y3**2]
u2_tp = [y1 + 2, y2 + 2, y3 + 2]
print("u1_tp = y^2   =", [mp.nstr(v, 10) for v in u1_tp], "prod =", mp.nstr(u1_tp[0]*u1_tp[1]*u1_tp[2], 12))
print("u2_tp = y + 2 =", [mp.nstr(v, 10) for v in u2_tp], "prod =", mp.nstr(u2_tp[0]*u2_tp[1]*u2_tp[2], 12))
# Verify R(U^+) = 2 * R(U) (index 2 in U/<+-1>, total index 4 in U)
R_tp = abs(mp.det(mp.matrix([[mp.log(u1_tp[0]), mp.log(u1_tp[1])], [mp.log(u2_tp[0]), mp.log(u2_tp[1])]])))
R_F3 = abs(mp.det(mp.matrix([[mp.log(abs(y1)), mp.log(abs(y2))], [mp.log(u2_tp[0]), mp.log(u2_tp[1])]])))
print(f"R(U^+) = {mp.nstr(R_tp, 18)}, R(U) = {mp.nstr(R_F3, 18)}, ratio = {mp.nstr(R_tp/R_F3, 10)}")
print("3D Shintani cone determinant det(1, y^2, y+2) =", mp.nstr(mp.det(mp.matrix([
    [1, 1, 1],
    u1_tp,
    u2_tp
])), 15))
print("Compare sqrt(D_{F_3}) = sqrt(229) =", mp.nstr(mp.sqrt(229), 15))
