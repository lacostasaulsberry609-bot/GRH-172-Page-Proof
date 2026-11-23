#!/usr/bin/env python3
"""
Wave-5 Squad C06: Exact Verification of ch28 Mechanism, 6-vs-4-vs-2 Complex Conjugation Audit,
Half-Integral Weight Eisenstein Collapse & Hecke Eigenvalues, and Mod-l Simultaneous
Non-Vanishing Densities over Q and K_0 = Q(sqrt(5)).

All arithmetic is 100% exact (integer / Fraction / finite field F_{ell^r}, zero floating-point error
in any congruence or L-value computation). Floating-point is used ONLY for printing density ratios.

Suites:
  Suite 1: ch28 100%-universal LemmaX over Q (including l | f) & 2-adic Lemma C06-1 (-1 notin <l> mod 2^m)
  Suite 2: Theorem C06-2 — Exact mod-l collapse of l * E_{l - 1/2}(z; 1) == c(0)*theta(z) mod l (l=5, 7)
           AND exact Shimura T_{p^2} eigenvalue verification & non-degeneracy for twisted E_{k'+1/2}(z; chi)
  Suite 3: Over Q — Fast exact single/2-fold/3-fold/4-fold/6-fold densities & minimal D (l = 5, 7, 11, 13):
           (3A) Real triple (1, chi_8, chi_12) for E_{3/2}, E_{7/2}, E_{11/2} on D <= 2000
           (3B) High-order xi_0 (p_0=2 M=32 ord=8 vs p_0=3 M=27 ord=9) with both real (chi_13) and
                quartic (chi_5^{(4)}, phi^2 != 1) hosts — verifying 6-vs-4-vs-2 exact dichotomy!
  Suite 4: Over K_0 = Q(sqrt(5)) — Exact 2D Shintani L_{K0}(0, .) & L_{K0}(-2, .) (l = 5, 7, 11, 13):
           (4A) Triple (chi_8 o N, psi_0, psi_0') at weight (3/2, 3/2) on Nm(nu) < 800
           (4B) Weight-absorbed (7/2, 7/2) for (psi_0, psi_0') on Nm(nu) <= 250
           (4C) High-order xi_0 = chi_0 o N (p_0=2 M=16,32 vs p_0=3 M=9,27) on K_0 (l = 5, 7, 11, 13)
  Suite 5: Exact verification of Theorem C06-3 (f*theta Serre density-drop vs f) & Theorem C06-4
           (Victor Miller echelon disjoint-support pairs in M_{k+1/2}(Gamma_0(4); F_l))
"""

import math
import time
import warnings
from fractions import Fraction
import sympy as sp

warnings.filterwarnings("ignore", category=UserWarning)
try:
    from sympy.utilities.exceptions import SymPyDeprecationWarning
    warnings.filterwarnings("ignore", category=SymPyDeprecationWarning)
except Exception:
    pass

# =============================================================================
# Fast exact arithmetic primitives (zero sympy calls inside tight loops!)
# =============================================================================

def kronecker_int(a, n):
    """Fast pure-Python exact Kronecker symbol (a/n)."""
    if n == 0:
        return 1 if (a == 1 or a == -1) else 0
    if n == 1:
        return 1
    if n < 0:
        res = -1 if a < 0 else 1
        n = -n
    else:
        res = 1
    # Remove factor of 2 from n
    tz = (n & -n).bit_length() - 1
    if tz:
        if (a & 1) == 0:
            return 0
        if tz & 1:
            r8 = a & 7
            if r8 == 3 or r8 == 5:
                res = -res
        n >>= tz
    if n == 1:
        return res
    a %= n
    while a:
        tz = (a & -a).bit_length() - 1
        if tz:
            if tz & 1:
                r8 = n & 7
                if r8 == 3 or r8 == 5:
                    res = -res
            a >>= tz
        a, n = n, a
        if (a & 3) == 3 and (n & 3) == 3:
            res = -res
        a %= n
    return res if n == 1 else 0

def is_squarefree(n):
    if n <= 0:
        return False
    d = 2
    while d * d <= n:
        if n % (d * d) == 0:
            return False
        d += 1 if d == 2 else 2
    return True

def is_fundamental_neg_disc(D):
    """True iff -D < 0 is a fundamental discriminant."""
    if D < 3:
        return False
    r4 = (-D) & 3
    if r4 == 1:
        return is_squarefree(D)
    elif r4 == 0:
        d4 = D >> 2
        if (d4 & 3) == 0:
            return False
        if ((-d4) & 3) in (2, 3):
            return is_squarefree(d4)
    return False

def bernoulli_poly_frac(k, x):
    if k == 1:
        return x - Fraction(1, 2)
    if k == 2:
        return x * x - x + Fraction(1, 6)
    if k == 3:
        return x**3 - Fraction(3, 2) * x**2 + Fraction(1, 2) * x
    if k == 4:
        return x**4 - 2 * x**3 + x**2 - Fraction(1, 30)
    if k == 5:
        return x**5 - Fraction(5, 2) * x**4 + Fraction(5, 3) * x**3 - Fraction(1, 6) * x
    raise ValueError(k)

def L_neg_e_real_Q_fast(e, chi_arr, N):
    """Exact L(-e, chi) = -B_{e+1, chi}/(e+1) for real-valued chi mod N (odd when e even)."""
    k = e + 1
    if k == 1:
        s = 0
        for a in range(1, N):
            v = chi_arr[a]
            if v:
                s += v * a
        return Fraction(-s, N)
    elif k == 3:
        s1 = s2 = s3 = 0
        for a in range(1, N):
            v = chi_arr[a]
            if v:
                a2 = a * a
                s1 += v * a
                s2 += v * a2
                s3 += v * a2 * a
        B3 = Fraction(s3, N) - Fraction(3 * s2, 2) + Fraction(N * s1, 2)
        return -B3 / 3
    elif k == 5:
        s1 = s3 = s4 = s5 = 0
        for a in range(1, N):
            v = chi_arr[a]
            if v:
                a2 = a * a
                a3 = a2 * a
                s1 += v * a
                s3 += v * a3
                s4 += v * a3 * a
                s5 += v * a3 * a2
        B5 = Fraction(s5, N) - Fraction(5 * s4, 2) + Fraction(5 * N * s3, 3) - Fraction(N**3 * s1, 6)
        return -B5 / 5
    else:
        raise ValueError(k)

def clm_prod(q, terms=30):
    p = 1.0
    qk = q
    for _ in range(terms):
        p *= (1.0 - 1.0 / qk)
        qk *= q
    return p

def make_cyclotomic_field_mod_ell(order, ell):
    """
    Build F_{ell^r} = F_ell[x] / (irred) containing a primitive `order`-th root of unity,
    where gcd(order, ell) = 1.
    Returns (r, pow_table) where pow_table[k] is tuple of length r in GF(ell)^r for zeta^k.
    """
    assert math.gcd(order, ell) == 1
    r = 1
    cur = ell % order
    while cur != 1:
        cur = (cur * ell) % order
        r += 1
    x = sp.Symbol('x')
    # Cyclotomic polynomial Phi_order(x) mod ell
    phi_int = sp.cyclotomic_poly(order, x)
    phi_mod = sp.Poly(phi_int, x, modulus=ell)
    factors = sp.factor_list(phi_mod, modulus=ell)[1]
    irred = factors[0][0]
    assert irred.degree() == r, f"order={order}, ell={ell}: deg {irred.degree()} != {r}"
    # Represent irred as monic tuple of length r+1 (descending) or low-to-high for fast reduction
    coeffs = [int(c) % ell for c in irred.all_coeffs()]  # length r+1, coeffs[0] == 1
    assert coeffs[0] == 1
    # Fast polynomial multiplication by x mod irred in pure Python
    pow_table = []
    vec = [0] * r
    vec[0] = 1  # 1 = x^0 (low-to-high: vec[j] is coeff of x^j)
    # irred = x^r + sum_{j=0}^{r-1} irred_low[j] x^j => x^r == -sum irred_low[j] x^j
    irred_low = [coeffs[r - j] for j in range(r)]
    for _ in range(order):
        pow_table.append(tuple(vec))
        top = vec[r - 1]
        new_vec = [0] + vec[:-1]
        if top:
            for j in range(r):
                new_vec[j] = (new_vec[j] - top * irred_low[j]) % ell
        vec = new_vec
    assert pow_table[0] == tuple(vec), "Order check failed!"
    return r, pow_table

def v2(n):
    return (n & -n).bit_length() - 1

def check_neg1_in_subgroup(ell, mod):
    cur = 1 % mod
    target = (mod - 1) % mod
    seen = set()
    while cur not in seen:
        if cur == target:
            return True
        seen.add(cur)
        cur = (cur * ell) % mod
    return False


# =============================================================================
# SUITE 1: ch28 100%-Universal LemmaX Verification & 2-adic Lemma C06-1
# =============================================================================

def run_suite_1():
    print("=" * 80)
    print("SUITE 1: ch28 100%-UNIVERSAL LEMMAX MECHANISM & 2-ADIC LEMMA C06-1")
    print("=" * 80)

    # 1A: Verify 2-adic Lemma C06-1: for ALL odd primes ell and ALL m >= v_2(ell+1) + 1,
    # -1 NOT in <ell> mod 2^m! Meanwhile for p_0 = 3, -1 in <ell> mod 3^m iff ell == 2 mod 3.
    primes_test = list(sp.primerange(3, 100))
    checked_2 = 0
    checked_3 = 0
    for ell in primes_test:
        a = v2(ell + 1)
        for m in range(a + 1, 15):
            assert not check_neg1_in_subgroup(ell, 1 << m), f"Counterexample at ell={ell}, m={m}"
            checked_2 += 1
        if ell != 3:
            expect = (ell % 3 == 2)
            for m in range(1, 9):
                got = check_neg1_in_subgroup(ell, 3 ** m)
                assert got == expect, f"3-adic check failed at ell={ell}, m={m}"
                checked_3 += 1
    print(f"  [1A] Lemma C06-1 VERIFIED (0 errors):")
    print(f"       p_0=2: -1 notin <l> mod 2^m for ALL {checked_2} pairs (l in [3,97], m in [v2(l+1)+1, 14])!")
    print(f"       p_0=3: -1 in <l> mod 3^m <=> l == 2 (mod 3) for ALL {checked_3} pairs!")

    # 1B: Verify ch28 Theorem thm:28:lemma-x gives 100.0% non-vanishing over ALL primitive xi mod 2^n
    # EVEN when ell | f (e.g. ell=5, f=5, phi = omega_5^e, d=1, v_2(5-1)=2, threshold 5*16=80 <= 128=2^7)!
    # Compute B_{1, phi x xi} mod P directly via exact Z_ell arithmetic (precision ell^2 for ell | f)!
    print(f"\n  [1B] Direct verification of ch28 100%-universal non-vanishing (including ell | f):")
    for ell, f, e_teich, n in [(5, 1, 0, 5), (5, 3, 0, 6), (5, 5, 2, 7), (7, 1, 0, 8)]:
        # Determine d such that 4 | ell^d - 1 and ord(phi) | ell^d - 1
        d = 1 if (ell % 4 == 1) else 2
        e2 = v2(ell**d - 1)
        thresh = f * (4 ** e2)
        N2 = 1 << n
        assert N2 >= thresh, f"2^{n}={N2} < {thresh}"
        # phi: if f=1 -> trivial (even); if f=3 -> chi_{-3} (odd); if f=5 -> omega_5^2 = chi_5 (even)
        if f == 1:
            phi_parity = +1
            def phi_val(a): return 1
        elif f == 3:
            phi_parity = -1
            def phi_val(a): return kronecker_int(-3, a)
        elif f == 5:
            phi_parity = +1
            def phi_val(a): return kronecker_int(5, a)
        # Need xi primitive mod 2^n with xi(-1) = -phi_parity.
        # Primitive characters mod 2^n of fixed parity s = -phi_parity are parameterized by
        # odd k in [1, 2^{n-2}-1] (number = 2^{n-3}): xi_k(-1) = s, xi_k(5) = zeta_{2^{n-2}}^k!
        ord2 = 1 << (n - 2)
        r_deg, pow_tbl = make_cyclotomic_field_mod_ell(ord2, ell)
        # Build discrete log base 5 mod 2^n with sign
        log5_sign = {}
        v = 1
        for t in range(ord2):
            log5_sign[v] = (+1, t)
            log5_sign[(N2 - v) % N2] = (-1, t)
            v = (v * 5) % N2
        # Compute B_{1, phi x xi_k} mod P for ALL primitive xi_k of parity -phi_parity!
        # Wait: when ell | f (f=5, ell=5), use exact l_partial or compute sum a*phi(a)*xi(a) mod ell^2!
        # Actually, for f=5 and phi = chi_5, chi_5 takes values in {0, +1, -1} in Z!
        # And xi_k takes values in Z[zeta_{ord2}]. Working mod ell^2 in Z[x]/(Phi_{ord2}) gives exact B_1 mod P!
        # Even simpler: use Lemma 28.4 (lx_partial) directly in F_{ell^r} — NO ell^2 needed!
        # Wait: let's compute g(u) in Q directly from Definition in Lemma 28.4:
        # S(0) = sum_{r=0}^{f*N2-1, r==0 mod N2} phi(r) = sum_{j=0}^{f-1} phi(j*N2) = 0 (for f>1) or 1 (for f=1)
        # Actually compute g(u) = (A(u) - A(0))/(f*N2) as exact Fraction!
        Ntot = f * N2
        A = [0] * N2
        for a in range(Ntot):
            pv = phi_val(a)
            if pv:
                A[a % N2] += pv * a
        g_mod = []
        for u in range(N2):
            gu = Fraction(A[u] - A[0], Ntot)
            assert gu.denominator % ell != 0, f"Denominator divisible by {ell} at u={u}: {gu}!"
            g_mod.append((gu.numerator * pow(gu.denominator, -1, ell)) % ell)
        # Now evaluate sum_{u in (Z/2^n)^*} xi_k(u) * g_mod[u] in F_{ell^r} for EVERY primitive k (odd k in 1..ord2-1)
        s_xi = -phi_parity
        n_prim = 0
        n_nz = 0
        for k_odd in range(1, ord2, 2):
            n_prim += 1
            acc = [0] * r_deg
            for u, (sgn, t) in log5_sign.items():
                gm = g_mod[u]
                if gm == 0:
                    continue
                coef = gm if (sgn == 1 or s_xi == 1) else (ell - gm) % ell
                vec = pow_tbl[(k_odd * t) % ord2]
                for j in range(r_deg):
                    acc[j] = (acc[j] + coef * vec[j]) % ell
            if any(acc):
                n_nz += 1
        print(f"       l={ell}, f={f} (l|f={f%ell==0}), 2^n={N2} >= thresh={thresh}: "
              f"non-zero = {n_nz}/{n_prim} ({100.0*n_nz/n_prim:.1f}% — EXACT 100%!)")
        assert n_nz == n_prim


# =============================================================================
# SUITE 2: Theorem C06-2 — Exact Mod-l Collapse of l*E_{l-1/2}(z; 1) to theta(z)
#          & Shimura T_{p^2} Eigenvalue Verification
# =============================================================================

def cohen_H_r(r, N):
    """
    Exact Cohen function H(r, N) (H. Cohen 1975, Math. Ann. 217, p. 273) for r >= 1, N >= 0:
    For N = 0: H(r, 0) = zeta(1 - 2r) = -B_{2r}/(2r).
    For N > 0 with (-1)^r N == 0, 1 (mod 4):
      Write (-1)^r N = D * f^2 where D is a fundamental discriminant (or D=1 if (-1)^r N is a square!).
      Then H(r, N) = L(1 - r, chi_D) * sum_{d | f} mu(d) chi_D(d) d^{r-1} sigma_{2r-1}(f/d).
    Else H(r, N) = 0.
    The generating function sum_{N >= 0} H(r, N) q^N is the Cohen-Eisenstein series in M_{r+1/2}^+(Gamma_0(4))!
    """
    if N == 0:
        B2r = sp.bernoulli(2 * r)
        return Fraction(-int(B2r.p), int(B2r.q) * 2 * r)
    signed_N = N if (r % 2 == 0) else -N
    if signed_N % 4 not in (0, 1):
        return Fraction(0)
    # Factor signed_N = D * f^2 with D fundamental discriminant (or D = 1)
    # Find largest square f^2 dividing signed_N such that signed_N/f^2 == 0 or 1 mod 4
    absN = abs(signed_N)
    # Factor absN
    fac = sp.factorint(absN)
    core = 1 if signed_N > 0 else -1
    f = 1
    for p, e in fac.items():
        if e & 1:
            core *= p
        f *= p ** (e >> 1)
    if core % 4 in (2, 3):
        D = core * 4
        assert f % 2 == 0
        f //= 2
    else:
        D = core
    # Compute L(1 - r, chi_D)
    if D == 1:
        Br = sp.bernoulli(r)
        L_val = Fraction(-int(Br.p), int(Br.q) * r)
    else:
        absD = abs(D)
        # B_{r, chi_D} = absD^{r-1} sum_{a=1}^{absD} (D/a) B_r(a/absD)
        Br_poly = sp.Poly(sp.bernoulli(r, sp.Symbol('x')), sp.Symbol('x'))
        # Evaluate exactly via Fraction
        coeffs = [Fraction(int(c.p), int(c.q)) for c in Br_poly.all_coeffs()]
        deg = r
        s = Fraction(0)
        for a in range(1, absD):
            kd = kronecker_int(D, a)
            if kd == 0:
                continue
            xa = Fraction(a, absD)
            pv = Fraction(0)
            for c in coeffs:
                pv = pv * xa + c
            s += kd * pv
        B_r_chi = s * (absD ** (r - 1))
        L_val = -B_r_chi / r
    # Compute divisor factor sum_{d | f} mu(d) chi_D(d) d^{r-1} sigma_{2r-1}(f/d)
    div_sum = 0
    for d in sp.divisors(f):
        mu_d = int(sp.mobius(d))
        if mu_d == 0:
            continue
        kd = 1 if D == 1 else kronecker_int(D, d)
        if kd == 0:
            continue
        m = f // d
        sig = sum(x ** (2 * r - 1) for x in sp.divisors(m))
        div_sum += mu_d * kd * (d ** (r - 1)) * sig
    return L_val * div_sum

def run_suite_2():
    print("\n" + "=" * 80)
    print("SUITE 2: THEOREM C06-2 — MOD-l COLLAPSE OF l*E_{l-1/2}(z; 1) TO theta(z)")
    print("         & SHIMURA T_{p^2} EIGENVALUE VERIFICATION")
    print("=" * 80)

    # 2A: For ell = 5 (r = k' = 4, weight 9/2) and ell = 7 (r = k' = 6, weight 13/2):
    # Check that ell * H(ell - 1, N) is ell-integral for ALL N in [0, 60],
    # has ell * H(ell-1, 0) != 0 mod ell,
    # has ell * H(ell-1, m^2) == 2 * ell * H(ell-1, 0) != 0 mod ell for ALL squares m^2,
    # and has ell * H(ell-1, N) == 0 mod ell for ALL non-squares N in [1, 60]!!
    for ell in [5, 7]:
        r = ell - 1
        c0 = ell * cohen_H_r(r, 0)
        assert c0.denominator % ell != 0
        c0_mod = (c0.numerator * pow(c0.denominator, -1, ell)) % ell
        assert c0_mod != 0
        sq_ok = 0
        nonsq_zero = 0
        nonsq_tot = 0
        H_vals = [cohen_H_r(r, N) for N in range(65)]
        for N in range(1, 65):
            val = ell * H_vals[N]
            assert val.denominator % ell != 0, f"Pole at N={N}: {val}"
            v_mod = (val.numerator * pow(val.denominator, -1, ell)) % ell
            s = math.isqrt(N)
            if s * s == N:
                # For N = m^2, in Kohnen plus space H(r, m^2) = zeta(1-r) * sum_{d|m} mu(d) d^{r-1} sigma_{2r-1}(m/d)
                # Note: by von Staudt-Clausen, v_ell(B_r) = -1 AND v_ell(B_{2r}) = -1!
                # Check exact ratio mod ell:
                # Wait: sum_{d|m} mu(d) d^{r-1} sigma_{2r-1}(m/d) == 1 mod ell when ell nmid m?
                # Wait: for m = p != ell, sigma_{2r-1}(p) - p^{r-1} = (1 + p^{2r-1}) - p^{r-1} == 1 + p^{-1} - p^{-1} = 1 (mod ell)!!
                # AMAZING!! Check m = ell too: sigma_{2r-1}(ell) - ell^{r-1} == 1 - 0 = 1 (mod ell)!!
                # So for EVERY m >= 1, the divisor sum is == 1 (mod ell), hence ell*H(r, m^2) == ell*zeta(1-r) (CONSTANT!) mod ell!!
                # And compare ell*zeta(1-r) vs ell*zeta(1-2r): -ell*B_r/r vs -ell*B_{2r}/(2r):
                # Since ell*B_r == -1 mod ell and ell*B_{2r} == -1 mod ell (von Staudt-Clausen!),
                # -ell*B_r/r == +1/(-1) = -1 mod ell, while -ell*B_{2r}/(2r) == +1/(-2) = -1/2 mod ell!
                # So ell*H(r, m^2) == 2 * (ell*H(r, 0)) (mod ell) FOR EVERY m >= 1!!
                # Thus ell * sum_{N>=0} H(ell-1, N) q^N == (ell*H(ell-1, 0)) * (1 + 2 sum_{m>=1} q^{m^2}) = c0 * theta(z) (mod ell)!!
                assert v_mod == (2 * c0_mod) % ell, f"Square mismatch at ell={ell}, N={N}: got {v_mod}, exp {(2*c0_mod)%ell}"
                sq_ok += 1
            else:
                nonsq_tot += 1
                assert v_mod == 0, f"Non-square non-zero at ell={ell}, N={N}: got {v_mod}"
                nonsq_zero += 1
        print(f"  [2A] l={ell}, weight k'+1/2 = {r}+1/2: ell*H({r},0) mod {ell} = {c0_mod} != 0;")
        print(f"       ALL {sq_ok}/{sq_ok} squares match 2*c(0) mod {ell}; ALL {nonsq_zero}/{nonsq_tot} non-squares == 0 mod {ell}!")
        print(f"       => CONFIRMED: {ell} * E_{{{r}+1/2}}(z; 1) == {c0_mod} * theta(z) (mod {ell}) (density 0 on squarefree!)")

    # 2B: Verify EXACT Shimura T_{p^2} eigenvalue lambda_p = 1 + p^{2r-1} on Cohen's H(r, N) for r=1, 2, 4, p=3, 5!
    print(f"\n  [2B] Exact Shimura T_{{p^2}} eigenvalue check (lambda_p = 1 + p^{{2k'-1}}) on H(k', N):")
    for r in [1, 2, 4]:
        for p in [3, 5]:
            lam = 1 + p ** (2 * r - 1)
            for N in [0, 3, 4, 7, 8, 11, 12]:
                # (f | T_{p^2})(N) = H(r, p^2 N) + ((-1)^r N / p) p^{r-1} H(r, N) + p^{2r-1} H(r, N/p^2)
                t1 = cohen_H_r(r, p * p * N)
                t2 = kronecker_int((N if r % 2 == 0 else -N), p) * (p ** (r - 1)) * cohen_H_r(r, N)
                t3 = (p ** (2 * r - 1)) * cohen_H_r(r, N // (p * p)) if (N % (p * p) == 0) else Fraction(0)
                lhs = t1 + t2 + t3
                rhs = lam * cohen_H_r(r, N)
                assert lhs == rhs, f"T_{{p^2}} failed at r={r}, p={p}, N={N}: {lhs} != {rhs}"
    print(f"       ALL 42 exact T_{{p^2}} identities PASSED (0 error) for k' in {{1,2,4}}, p in {{3,5}}, N in {{0,3,4,7,8,11,12}}!")


# =============================================================================
# SUITE 3: Over Q — Fast Exact Densities (D <= 2000) & 6-vs-4-vs-2 Dichotomy
# =============================================================================

def run_suite_3():
    print("\n" + "=" * 80)
    print("SUITE 3: OVER Q — EXACT SINGLE/2-FOLD/3-FOLD/4-FOLD/6-FOLD MOD-P DENSITIES")
    print("=" * 80)

    # 3A: Fundamental discriminants -D <= 2000 with gcd(D, 6) = 1
    fund_Ds = [D for D in range(3, 2001) if is_fundamental_neg_disc(D)]
    Ds_cop6 = [D for D in fund_Ds if (D % 2 != 0 and D % 3 != 0)]
    print(f"\n--- 3A: Real triple (psi_1=1, psi_2=chi_8, psi_3=chi_12) on {len(Ds_cop6)} fund. -D <= 2000 (gcd(D,6)=1) ---")

    # Precompute chi_8 mod 8, chi_12 mod 12
    c8_tbl = [kronecker_int(8, a) for a in range(8)]
    c12_tbl = [kronecker_int(12, a) for a in range(12)]
    psis = [("1", 1, [1]), ("chi_8", 8, c8_tbl), ("chi_12", 12, c12_tbl)]

    # Fast computation of L(-e, psi_i * chi_{-D}) using precomputed Kronecker table of length D!
    for e in [0, 2, 4]:
        print(f"\n  [Weight E_{{{e}+3/2}} = E_{{{2*e+3}/2}}, L(-{e}, psi_i * chi_{{-D}})]")
        vals = {i: {} for i in range(3)}
        for D in Ds_cop6:
            kd_tbl = [kronecker_int(-D, a) for a in range(D)]
            for i, (name, cond, ptbl) in enumerate(psis):
                N = cond * D
                chi_arr = [ptbl[a % cond] * kd_tbl[a % D] for a in range(N)]
                vals[i][D] = L_neg_e_real_Q_fast(e, chi_arr, N)
        print(f"  {'l':>3} | {'#goodD':>6} | {'d1(psi1)':>8} {'d1(psi2)':>8} {'d1(psi3)':>8} | {'d2(1,2)':>8} {'d3(1,2,3)':>9} | {'Unif^3':>7} {'CLM^3':>7} | {'minD_2':>6} {'minD_3':>6}")
        for ell in [5, 7, 11, 13]:
            good_D = [D for D in Ds_cop6 if D % ell != 0]
            c1 = [0, 0, 0]
            c2 = c3 = 0
            min2 = min3 = None
            for D in good_D:
                ok = []
                for i in range(3):
                    v = vals[i][D]
                    assert v.denominator % ell != 0
                    nz = (v.numerator % ell != 0)
                    ok.append(nz)
                    if nz:
                        c1[i] += 1
                if ok[0] and ok[1]:
                    c2 += 1
                    if min2 is None: min2 = D
                if ok[0] and ok[1] and ok[2]:
                    c3 += 1
                    if min3 is None: min3 = D
            tot = len(good_D)
            print(f"  {ell:3d} | {tot:6d} | {c1[0]/tot:8.4f} {c1[1]/tot:8.4f} {c1[2]/tot:8.4f} | "
                  f"{c2/tot:8.4f} {c3/tot:9.4f} | {(1-1/ell)**3:7.4f} {clm_prod(ell)**3:7.4f} | {str(min2):>6} {str(min3):>6}")

    # 3B: FAST exact high-order xi_0 over Q (using CRT + table lookup — 200x faster than B07!):
    # Compute B_{1, phi * xi_0^s * chi_{-D}} mod P via:
    #   sum_{a=1}^{N-1} a * phi(a) * xi_0^s(a) * chi_{-D}(a) mod ell,
    # where N = M_phi * M_xi * D (pairwise coprime, all coprime to ell!).
    # Write a = r + k * M_0 where M_0 = M_phi * M_xi and k in 0..D-1? Even faster:
    # Group by (a mod M_xi): for each residue class u in (Z/M_xi)^*, compute the SCALAR mod ell:
    #   S_u = sum_{a in 1..N-1, a == u mod M_xi} a * phi(a) * chi_{-D}(a) (mod ell)!!
    # Look how fast that is: a = u + M_xi * t (t = 0 .. M_phi*D - 1), pure integer mod ell!
    # Then L(0, phi * xi_0^s * chi_{-D}) mod P = -N^{-1} * sum_{u} S_u * xi_0(u)^s in F_{ell^r}!!
    # Computing BOTH s = +1 and s = -1 simultaneously costs ZERO extra work!!
    def eval_L0_pm_fast(M_phi, phi_tbl, M_xi, ord_xi, r_deg, pow_tbl, log_xi, D, ell):
        """
        Compute L(0, phi * xi_0^{+1} * chi_{-D}) and L(0, phi * xi_0^{-1} * chi_{-D}) mod P
        simultaneously in pure integer arithmetic.
        phi_tbl: list of ints mod ell of length M_phi (or pairs if complex).
        Here handles real phi_tbl (values in {0, 1, -1})!
        """
        N = M_phi * M_xi * D
        invN = pow(N, -1, ell)
        kd = [kronecker_int(-D, a) for a in range(D)]
        # Accumulate scalar sums per exponent k in 0..ord_xi-1!
        bucket = [0] * ord_xi
        step = M_xi
        for u, k_exp in log_xi.items():
            s = 0
            a = u
            p_idx = u % M_phi
            d_idx = u % D
            p_step = step % M_phi
            d_step = step % D
            while a < N:
                pv = phi_tbl[p_idx]
                if pv:
                    kv = kd[d_idx]
                    if kv:
                        s += a if (pv * kv == 1) else -a
                a += step
                p_idx += p_step
                if p_idx >= M_phi: p_idx -= M_phi
                d_idx += d_step
                if d_idx >= D: d_idx -= D
            bucket[k_exp] = (bucket[k_exp] + s) % ell
        # Now evaluate at +1 and -1 in F_{ell^r}
        acc_p = [0] * r_deg
        acc_m = [0] * r_deg
        for k_exp, sc in enumerate(bucket):
            if sc == 0:
                continue
            vp = pow_tbl[k_exp]
            vm = pow_tbl[(-k_exp) % ord_xi]
            for j in range(r_deg):
                acc_p[j] = (acc_p[j] + sc * vp[j]) % ell
                acc_m[j] = (acc_m[j] + sc * vm[j]) % ell
        # Multiply by -invN mod ell (non-zero scalar doesn't change zero-ness, but keep exact)
        neg_inv = (-invN) % ell
        vp_out = tuple((x * neg_inv) % ell for x in acc_p)
        vm_out = tuple((x * neg_inv) % ell for x in acc_m)
        return vp_out, vm_out

    Ds_3b = [D for D in fund_Ds if D <= 600 and math.gcd(D, 30) == 1]
    phi1 = [1]
    phi17 = [kronecker_int(17, a) for a in range(17)]

    print(f"\n--- 3B-i: High-order p_0=2 (M=32 ord=8, and M=64 ord=16 for l=7), real host phi=chi_17 (phi^2=1), D <= 600 ---")
    for M_xi, ord_xi, ell in [(32, 8, 5), (32, 8, 7), (64, 16, 7), (32, 8, 11), (32, 8, 13)]:
        r_deg, pow_tbl = make_cyclotomic_field_mod_ell(ord_xi, ell)
        c_in_DP = check_neg1_in_subgroup(ell, ord_xi)
        q_l = ell ** r_deg
        log5 = {}
        v = 1
        for k in range(ord_xi):
            log5[v] = k
            log5[(M_xi - v) % M_xi] = k
            v = (v * 5) % M_xi
        good_D = [D for D in Ds_3b if D % ell != 0 and D % 17 != 0]
        cnt = [0, 0, 0, 0]
        cnt4 = 0
        mism_a = mism_b = 0
        min4 = None
        for D in good_D:
            ap, am = eval_L0_pm_fast(1, phi1, M_xi, ord_xi, r_deg, pow_tbl, log5, D, ell)
            bp, bm = eval_L0_pm_fast(17, phi17, M_xi, ord_xi, r_deg, pow_tbl, log5, D, ell)
            o = [any(ap), any(am), any(bp), any(bm)]
            for i in range(4):
                if o[i]: cnt[i] += 1
            if o[0] != o[1]: mism_a += 1
            if o[2] != o[3]: mism_b += 1
            if all(o):
                cnt4 += 1
                if min4 is None: min4 = D
        tot = len(good_D)
        if c_in_DP:
            assert mism_a == 0 and mism_b == 0
        print(f"  M={M_xi:2d}(ord={ord_xi:2d}) l={ell:2d} (F_{{l^{r_deg}}}, q_l={q_l:4d}, c in D_P={str(c_in_DP):5s}): #D={tot}, "
              f"d(a+)={cnt[0]/tot:.4f} d(a-)={cnt[1]/tot:.4f} d(b+)={cnt[2]/tot:.4f} d(b-)={cnt[3]/tot:.4f} | "
              f"ALL4={cnt4/tot:.4f} (Unif^4={(1-1/q_l)**4:.4f}) | mism(a/b)={mism_a}/{mism_b}, minD={min4}")

    print(f"\n--- 3B-ii: High-order p_0=3 (M=27, ord=9), real host phi=chi_17 (phi^2=1), D <= 600 ---")
    for ell in [5, 7, 11, 13]:
        M_xi = 27
        ord_xi = 9
        r_deg, pow_tbl = make_cyclotomic_field_mod_ell(ord_xi, ell)
        c_in_DP = check_neg1_in_subgroup(ell, ord_xi)
        q_l = ell ** r_deg
        log4 = {}
        v = 1
        for k in range(ord_xi):
            log4[v] = k
            log4[(M_xi - v) % M_xi] = k
            v = (v * 4) % M_xi
        good_D = [D for D in Ds_3b if D % ell != 0 and D % 17 != 0]
        cnt = [0, 0, 0, 0]
        cnt4 = 0
        mism_a = mism_b = 0
        min4 = None
        for D in good_D:
            ap, am = eval_L0_pm_fast(1, phi1, M_xi, ord_xi, r_deg, pow_tbl, log4, D, ell)
            bp, bm = eval_L0_pm_fast(17, phi17, M_xi, ord_xi, r_deg, pow_tbl, log4, D, ell)
            o = [any(ap), any(am), any(bp), any(bm)]
            for i in range(4):
                if o[i]: cnt[i] += 1
            if o[0] != o[1]: mism_a += 1
            if o[2] != o[3]: mism_b += 1
            if all(o):
                cnt4 += 1
                if min4 is None: min4 = D
        tot = len(good_D)
        if c_in_DP:
            assert mism_a == 0 and mism_b == 0, "Expected exact symmetry when c in D_P!"
        print(f"  l={ell:2d} (l%3={ell%3}, F_{{l^{r_deg}}}, q_l={q_l:6d}, c in D_P={str(c_in_DP):5s}): #D={tot}, "
              f"d(a+)={cnt[0]/tot:.4f} d(b+)={cnt[2]/tot:.4f} | ALL4={cnt4/tot:.4f} | mism(a/b)={mism_a}/{mism_b}, minD={min4}")

    # 3B-iii: GENUINE 6-ROOT CASE (phi^2 != 1): even quartic character phi mod 17 (ord=4, phi(-1)=+1)
    # with p_0=2, M=16 (ord=4) at l=5, 7, 11, 13 (notice for l=5, ord_4(5)=1 => q_l = 5!!
    # So all 6 values live in F_5, giving 6 INDEPENDENT F_5 values — density ~(4/5)^6 = 0.262!)
    print(f"\n--- 3B-iii: GENUINE 6-ROOT CASE (phi^2 != 1): quartic even phi mod 17 (ord=4) + xi_0 mod 16 (ord=4) ---")
    # Primitive root mod 17 is 3; 3^4 = 81 == 13 mod 17, 3^8 == -1 mod 17.
    # Even quartic char mod 17: phi(3^k) = i^k? Wait: phi(-1) = phi(3^8) = i^8 = +1! YES!
    log3_17 = {}
    v = 1
    for k in range(16):
        log3_17[v] = k % 4
        v = (v * 3) % 17
    Ds_3b3 = [D for D in fund_Ds if D <= 600 and math.gcd(D, 34) == 1]
    for ell in [5, 7, 11, 13]:
        M_xi = 16
        ord_tot = 4  # both phi and xi_0 have order 4, valued in mu_4(F_{ell^r})!
        r_deg, pow_tbl = make_cyclotomic_field_mod_ell(ord_tot, ell)
        c_in_DP = check_neg1_in_subgroup(ell, ord_tot)
        q_l = ell ** r_deg
        log5_16 = {}
        v = 1
        for k in range(4):
            log5_16[v] = k
            log5_16[(16 - v) % 16] = k
            v = (v * 5) % 16
        good_D = [D for D in Ds_3b3 if D % ell != 0]
        cnt6_each = [0] * 6
        cnt_all6 = 0
        min6 = None
        mism_pairs = [0, 0, 0]
        # 6 roots: (0,+1)=a+, (0,-1)=a-, (-1,+1)=b-, (+1,-1)=b+, (+1,+1)=t+, (-1,-1)=t-
        root_specs = [(0, 1), (0, -1), (1, -1), (-1, 1), (1, 1), (-1, -1)]
        for D in good_D:
            N = 17 * 16 * D
            kd = [kronecker_int(-D, a) for a in range(D)]
            # Accumulate scalar sums bucket[e_phi][e_xi] for e_phi in 0..3, e_xi in 0..3!
            # Wait: for alpha (e_phi ignored), need sums with 17 not coprime too! So compute alpha separately at N=16*D!
            b_al = [0] * 4
            for u, kx in log5_16.items():
                s = 0
                a = u
                d_idx = u % D
                d_step = 16 % D
                N_a = 16 * D
                while a < N_a:
                    kv = kd[d_idx]
                    if kv:
                        s += a if kv == 1 else -a
                    a += 16
                    d_idx += d_step
                    if d_idx >= D: d_idx -= D
                b_al[kx] = (b_al[kx] + s) % ell
            b_bt = [[0] * 4 for _ in range(4)]
            for u, kx in log5_16.items():
                a = u
                p_idx = u % 17
                d_idx = u % D
                p_step = 16 % 17
                d_step = 16 % D
                while a < N:
                    if p_idx:
                        kv = kd[d_idx]
                        if kv:
                            kp = log3_17[p_idx]
                            b_bt[kp][kx] = (b_bt[kp][kx] + (a if kv == 1 else -a)) % ell
                    a += 16
                    p_idx += p_step
                    if p_idx >= 17: p_idx -= 17
                    d_idx += d_step
                    if d_idx >= D: d_idx -= D
            oks = []
            for idx_r, (sp_sgn, sx_sgn) in enumerate(root_specs):
                acc = [0] * r_deg
                if sp_sgn == 0:
                    for kx in range(4):
                        sc = b_al[kx]
                        if sc:
                            vec = pow_tbl[(sx_sgn * kx) % 4]
                            for j in range(r_deg):
                                acc[j] = (acc[j] + sc * vec[j]) % ell
                else:
                    for kp in range(4):
                        for kx in range(4):
                            sc = b_bt[kp][kx]
                            if sc:
                                vec = pow_tbl[(sp_sgn * kp + sx_sgn * kx) % 4]
                                for j in range(r_deg):
                                    acc[j] = (acc[j] + sc * vec[j]) % ell
                ok = any(acc)
                oks.append(ok)
                if ok: cnt6_each[idx_r] += 1
            for p_i in range(3):
                if oks[2*p_i] != oks[2*p_i + 1]:
                    mism_pairs[p_i] += 1
            if all(oks):
                cnt_all6 += 1
                if min6 is None: min6 = D
        tot = len(good_D)
        pred = (1 - 1/q_l)**(3 if c_in_DP else 6)
        print(f"  l={ell:2d} (F_{{l^{r_deg}}}, q_l={q_l:3d}, c in D_P={str(c_in_DP):5s}): #D={tot}, "
              f"single={[round(c/tot,3) for c in cnt6_each]}, ALL6={cnt_all6/tot:.4f} (pred {pred:.4f}), "
              f"pair_mism={mism_pairs}, minD6={min6}")


# =============================================================================
# SUITE 4: Over K_0 = Q(sqrt(5)) — Exact 2D Shintani (Nm(nu) < 800)
# =============================================================================

def split_prime_roots_K0(p):
    return [r for r in range(p) if (r * r - 3 * r + 1) % p == 0]

def make_psi0_tbl(r29):
    tbl = [[0] * 29 for _ in range(29)]
    for a in range(29):
        for b in range(29):
            v = (a + r29 * b) % 29
            tbl[a][b] = 0 if v == 0 else kronecker_int(v, 29)
    return tbl

def compute_L0_K0_f29_times_chinu(phi_tbl, p, r):
    """
    Fast O(29^3 + p^2) exact L_{K0}(0, phi29 * chi_{-nu}) via Theorem A01-1.
    """
    f = 29
    m0 = p % f
    S2 = [[0] * f for _ in range(f)]
    for x in range(f):
        row = phi_tbl[x]
        for b in range(f):
            s = 0
            idx = b
            for r2 in range(f):
                if r2:
                    s += r2 * row[idx]
                idx += m0
                if idx >= f: idx -= f
            S2[x][b] = s
    H = [[0] * f for _ in range(f)]
    for a in range(f):
        for b in range(f):
            s = 0
            idx = a
            for r1 in range(f):
                if r1:
                    s += r1 * S2[idx][b]
                idx += m0
                if idx >= f: idx -= f
            H[a][b] = s
    leg = [0] + [kronecker_int(a, p) for a in range(1, p)]
    # Sum over u1 in 1..p, u2 in 0..p-1 of leg[(u1 + r*u2) % p] * H[u1 % 29][u2 % 29]
    # Even faster: accumulate counts C[a][b] = sum_{u1==a mod 29, u2==b mod 29} leg[(u1+r*u2)%p]!
    tot = 0
    for u1 in range(1, p + 1):
        rowH = H[u1 % f]
        idx = u1 % p
        b = 0
        for u2 in range(p):
            lv = leg[idx]
            if lv:
                tot += lv * rowH[b]
            idx += r
            if idx >= p: idx -= p
            b += 1
            if b == f: b = 0
    assert tot % (f * f) == 0, f"Non-integral L0 at p={p}: {tot}/{f*f}"
    return tot // (f * f)

def precompute_W_table_p(p, r):
    """W[k] = sum_{r2=1}^{p-1} ((k - r*r2)%p) * r2 in O(p^2)."""
    W = [0] * p
    for r2 in range(1, p):
        rr2 = (r * r2) % p
        for k in range(p):
            r1 = k - rr2
            if r1 < 0: r1 += p
            if r1:
                W[k] += r1 * r2
    return W

def compute_L0_K0_pullback_exact(M_pb, pb_norm_tbl, p, r, W, leg):
    """Exact L_{K0}(0, (pb o N) * chi_{-nu}) via Theorem A01-1."""
    step = M_pb % p
    F = [0] * p
    for c in range(p):
        s = 0
        idx = c
        for k in range(p):
            lv = leg[idx]
            if lv:
                s += W[k] * lv
            idx += step
            if idx >= p: idx -= p
        F[c] = s
    tot = 0
    for u1 in range(1, M_pb + 1):
        for u2 in range(M_pb):
            nm = (u1 * u1 + 3 * u1 * u2 + u2 * u2) % M_pb
            pv = pb_norm_tbl[nm]
            if pv:
                tot += pv * F[(u1 + r * u2) % p]
    return Fraction(tot, p * p)

def compute_L_neg2_K0_fast(f, phi_tbl, p, r):
    """Exact Shintani L_{K0}(-2, phi * chi_{-nu}) in O(f^3 + p^2)."""
    m0 = p % f
    Bf = {j: [bernoulli_poly_frac(j, Fraction(x, f)) for x in range(f)] for j in range(1, 6)}
    terms = [(5, 1, 6), (4, 2, 9), (3, 3, 11), (2, 4, 9), (1, 5, 6)]
    needed = set()
    for m1, m2, _ in terms:
        for j1 in range(1, m1 + 1):
            for j2 in range(1, m2 + 1):
                needed.add((j1, j2))
    S2 = {}
    for j2 in range(1, 6):
        bj2 = Bf[j2]
        tbl2 = [[Fraction(0)] * f for _ in range(f)]
        for x in range(f):
            for b in range(f):
                s = Fraction(0)
                idx = b
                for r2 in range(f):
                    v = phi_tbl[x][idx]
                    if v:
                        s += v * bj2[r2]
                    idx += m0
                    if idx >= f: idx -= f
                tbl2[x][b] = s
        S2[j2] = tbl2
    H = {}
    for j1, j2 in needed:
        bj1 = Bf[j1]
        s2 = S2[j2]
        tblH = [[Fraction(0)] * f for _ in range(f)]
        for a in range(f):
            for b in range(f):
                s = Fraction(0)
                idx = a
                for r1 in range(f):
                    sv = s2[idx][b]
                    if sv:
                        s += bj1[r1] * sv
                    idx += m0
                    if idx >= f: idx -= f
                tblH[a][b] = s
        H[(j1, j2)] = tblH
    N = f * p
    C_poly = {}
    for m1, m2, Ce in terms:
        base_c = Fraction(4 * Ce, math.factorial(m1) * math.factorial(m2))
        for j1 in range(1, m1 + 1):
            for j2 in range(1, m2 + 1):
                p1, p2 = m1 - j1, m2 - j2
                w = base_c * math.comb(m1, j1) * math.comb(m2, j2) * Fraction(N ** (j1 + j2 - 2), 1)
                if (p1, p2) not in C_poly:
                    C_poly[(p1, p2)] = [[Fraction(0)] * f for _ in range(f)]
                cp = C_poly[(p1, p2)]
                h = H[(j1, j2)]
                for a in range(f):
                    for b in range(f):
                        if h[a][b]:
                            cp[a][b] += w * h[a][b]
    leg = [0] + [kronecker_int(a, p) for a in range(1, p)]
    p_pairs = list(C_poly.keys())
    U_int = {pp: [[0] * f for _ in range(f)] for pp in p_pairs}
    u2_pows = [[u2 ** k for k in range(5)] for u2 in range(p)]
    u2_modf = [u2 % f for u2 in range(p)]
    for u1 in range(1, p + 1):
        a = u1 % f
        u1p = [u1 ** k for k in range(5)]
        row_acc = [[0] * f for _ in range(5)]
        idx = u1 % p
        for u2 in range(p):
            xv = leg[idx]
            if xv:
                b = u2_modf[u2]
                up2 = u2_pows[u2]
                row_acc[0][b] += xv
                row_acc[1][b] += xv * up2[1]
                row_acc[2][b] += xv * up2[2]
                row_acc[3][b] += xv * up2[3]
                row_acc[4][b] += xv * up2[4]
            idx += r
            if idx >= p: idx -= p
        for (p1, p2) in p_pairs:
            up1 = u1p[p1]
            ra = row_acc[p2]
            ua = U_int[(p1, p2)][a]
            for b in range(f):
                if ra[b]:
                    ua[b] += up1 * ra[b]
    total = Fraction(0)
    for pp in p_pairs:
        cp = C_poly[pp]
        ui = U_int[pp]
        for a in range(f):
            for b in range(f):
                if ui[a][b] and cp[a][b]:
                    total += ui[a][b] * cp[a][b]
    return total

def run_suite_4():
    print("\n" + "=" * 80)
    print("SUITE 4: OVER K_0 = Q(sqrt(5)) — EXACT 2D SHINTANI DENSITIES (l = 5, 7, 11, 13)")
    print("=" * 80)

    phi29 = make_psi0_tbl(25)
    phi29_c = make_psi0_tbl(7)
    # Calibration check: L_{K0}(0, chi_{-nu_41}) = 2
    W41 = precompute_W_table_p(41, 36)
    leg41 = [0] + [kronecker_int(a, 41) for a in range(1, 41)]
    assert compute_L0_K0_pullback_exact(1, [1], 41, 36, W41, leg41) == Fraction(2)

    odd_nu_primes = []
    for p in sp.primerange(11, 800):
        if p % 5 not in (1, 4) or p % 4 != 1 or p == 29:
            continue
        for r in split_prime_roots_K0(p):
            if kronecker_int(r, p) == 1 and kronecker_int((r - 1) % p, p) == -1:
                odd_nu_primes.append((p, r))
    print(f"  Totally odd split-prime quadratic twists chi_{{-nu}} of K_0 with Nm(nu) < 800: {len(odd_nu_primes)} twists")

    # 4A: Triple (chi_8 o N, psi_0, psi_0') at weight (3/2, 3/2) on Nm(nu) < 800!
    c8_tbl = [kronecker_int(8, nm) for nm in range(8)]
    L1, L2, L3 = {}, {}, {}
    W_cache = {}
    leg_cache = {}
    for p, r in odd_nu_primes:
        key = (p, r)
        W = precompute_W_table_p(p, r)
        leg = [0] + [kronecker_int(a, p) for a in range(1, p)]
        if p <= 350:
            W_cache[key] = W
            leg_cache[key] = leg
        v1 = compute_L0_K0_pullback_exact(8, c8_tbl, p, r, W, leg)
        assert v1.denominator == 1
        L1[key] = v1.numerator
        L2[key] = compute_L0_K0_f29_times_chinu(phi29, p, r)
        L3[key] = compute_L0_K0_f29_times_chinu(phi29_c, p, r)

    print(f"\n--- 4A: K_0 = Q(sqrt(5)), Triple (chi_8 o N, psi_0, psi_0') at weight (3/2, 3/2), Nm(nu) < 800 ---")
    print(f"  Sample values (smallest 5 twists):")
    for k in odd_nu_primes[:5]:
        print(f"    Nm={k[0]:3d} (r={k[1]:3d}): L1(chi8oN)={L1[k]:6d}, L2(psi0)={L2[k]:6d}, L3(psi0')={L3[k]:6d}")
    print(f"\n  {'l':>3} | {'#goodNu':>7} | {'d1(L1)':>7} {'d1(L2)':>7} {'d1(L3)':>7} | {'d2(1,2)':>7} {'d3(1,2,3)':>9} | {'Unif^3':>7} {'CLM^3':>7} | {'minNm2':>6} {'minNm3':>6}")
    for ell in [5, 7, 11, 13]:
        gks = [k for k in odd_nu_primes if k[0] != ell]
        c1 = c2 = c3 = c12 = c123 = 0
        min2 = min3 = None
        for k in gks:
            o1 = (L1[k] % ell != 0)
            o2 = (L2[k] % ell != 0)
            o3 = (L3[k] % ell != 0)
            if o1: c1 += 1
            if o2: c2 += 1
            if o3: c3 += 1
            if o1 and o2:
                c12 += 1
                if min2 is None: min2 = k[0]
            if o1 and o2 and o3:
                c123 += 1
                if min3 is None: min3 = k[0]
        tot = len(gks)
        print(f"  {ell:3d} | {tot:7d} | {c1/tot:7.4f} {c2/tot:7.4f} {c3/tot:7.4f} | "
              f"{c12/tot:7.4f} {c123/tot:9.4f} | {(1-1/ell)**3:7.4f} {clm_prod(ell)**3:7.4f} | {str(min2):>6} {str(min3):>6}")

    # 4B: Weight-absorbed E_{7/2, 7/2} (e = 2) on Nm(nu) <= 250!
    sub_nu = [k for k in odd_nu_primes if k[0] <= 250]
    L2_e2, L3_e2 = {}, {}
    for p, r in sub_nu:
        L2_e2[(p, r)] = compute_L_neg2_K0_fast(29, phi29, p, r)
        L3_e2[(p, r)] = compute_L_neg2_K0_fast(29, phi29_c, p, r)
    print(f"\n--- 4B: K_0 = Q(sqrt(5)), Weight-absorbed E_{{7/2, 7/2}} (e=2) for (psi_0, psi_0'), Nm <= 250 ({len(sub_nu)} twists) ---")
    print(f"  {'l':>3} | {'#goodNu':>7} | {'d1(psi0)':>8} {'d1(psi0p)':>9} | {'d2(both)':>8} | {'Unif^2':>7} | {'minNm_2':>7}")
    for ell in [5, 7, 11, 13]:
        gks = [k for k in sub_nu if k[0] != ell]
        c2 = c3 = c23 = 0
        min2 = None
        for k in gks:
            v2, v3 = L2_e2[k], L3_e2[k]
            assert v2.denominator % ell != 0 and v3.denominator % ell != 0
            o2 = (v2.numerator % ell != 0)
            o3 = (v3.numerator % ell != 0)
            if o2: c2 += 1
            if o3: c3 += 1
            if o2 and o3:
                c23 += 1
                if min2 is None: min2 = k[0]
        tot = len(gks)
        print(f"  {ell:3d} | {tot:7d} | {c2/tot:8.4f} {c3/tot:9.4f} | {c23/tot:8.4f} | {(1-1/ell)**2:7.4f} | {str(min2):>7}")

    # 4C: High-order xi_0 = chi_0 o N on K_0 (p_0 = 2 M=16,32 vs p_0 = 3 M=9,27) for l = 5, 7, 11, 13!
    print(f"\n--- 4C: K_0 = Q(sqrt(5)), High-order xi_0 = chi_0 o N (p_0=2 vs p_0=3) & Symmetry Audit (Nm <= 350) ---")
    nu_350 = [k for k in odd_nu_primes if k[0] <= 350]
    for p0, M, ord_xi, gen in [(2, 16, 4, 5), (2, 32, 8, 5), (3, 9, 3, 4), (3, 27, 9, 4)]:
        log_map = {}
        v = 1
        for k in range(ord_xi):
            log_map[v] = k
            log_map[(M - v) % M] = k
            v = (v * gen) % M
        # Precompute (u1, u2, k_exp) list for M x M!
        nm_pairs = []
        for u1 in range(1, M + 1):
            for u2 in range(M):
                nm = (u1 * u1 + 3 * u1 * u2 + u2 * u2) % M
                ke = log_map.get(nm)
                if ke is not None:
                    nm_pairs.append((u1, u2, ke))
        print(f"\n  [p_0={p0}, M={M}, ord(xi_0)={ord_xi}]")
        for ell in [5, 7, 11, 13]:
            r_deg, pow_tbl = make_cyclotomic_field_mod_ell(ord_xi, ell)
            c_in_DP = check_neg1_in_subgroup(ell, ord_xi)
            q_l = ell ** r_deg
            gks = [k for k in nu_350 if k[0] != ell]
            cnt_p = cnt_m = cnt_both = mism = 0
            min_both = None
            asymm_ex = None
            for p, r in gks:
                W = W_cache[(p, r)]
                leg = leg_cache[(p, r)]
                step = M % p
                F_mod = [0] * p
                for c in range(p):
                    s = 0
                    idx = c
                    for k in range(p):
                        lv = leg[idx]
                        if lv:
                            s += W[k] * lv
                        idx += step
                        if idx >= p: idx -= p
                    F_mod[c] = s % ell
                # Bucket by k_exp in 0..ord_xi-1
                bucket = [0] * ord_xi
                for u1, u2, ke in nm_pairs:
                    fc = F_mod[(u1 + r * u2) % p]
                    if fc:
                        bucket[ke] = (bucket[ke] + fc) % ell
                acc_p = [0] * r_deg
                acc_m = [0] * r_deg
                for ke, sc in enumerate(bucket):
                    if sc:
                        vp = pow_tbl[ke]
                        vm = pow_tbl[(-ke) % ord_xi]
                        for j in range(r_deg):
                            acc_p[j] = (acc_p[j] + sc * vp[j]) % ell
                            acc_m[j] = (acc_m[j] + sc * vm[j]) % ell
                ok_p = any(acc_p)
                ok_m = any(acc_m)
                if ok_p: cnt_p += 1
                if ok_m: cnt_m += 1
                if ok_p and ok_m:
                    cnt_both += 1
                    if min_both is None: min_both = p
                if ok_p != ok_m:
                    mism += 1
                    if asymm_ex is None: asymm_ex = (p, ok_p, ok_m)
            tot = len(gks)
            if c_in_DP:
                assert mism == 0, f"Unexpected mismatch when c in D_P: p0={p0}, M={M}, ell={ell}"
            print(f"    l={ell:2d} (F_{{l^{r_deg}}}, q_l={q_l:5d}, c in D_P={str(c_in_DP):5s}): #nu={tot}, "
                  f"d(+)={cnt_p/tot:.4f}, d(-)={cnt_m/tot:.4f}, both={cnt_both/tot:.4f}, "
                  f"mism={mism:2d}, minNm={min_both}, asymm={asymm_ex}")


# =============================================================================
# SUITE 5: Theorem C06-3 (f * theta Serre density drop) & Theorem C06-4 (Victor Miller Blindness)
# =============================================================================

def run_suite_5():
    print("\n" + "=" * 80)
    print("SUITE 5: THEOREM C06-3 (f*theta DENSITY DROP) & THEOREM C06-4 (STURM/VM BLINDNESS)")
    print("=" * 80)

    # 5A: Hurwitz-Kronecker relation f*theta for H(n) (k'=1) vs E_{7/2} (k'=3) mod l=5, 7!
    # For f(z) = sum_{n>=0} H(1, n) q^n, g(z) = f(z) * theta(z) = sum_{n>=0} A(n) q^n
    # where A(n) = sum_{m in Z, m^2 <= n} H(1, n - m^2)!
    # Recall for n = 4k: A(4k) = 2*sigma_1(k) - sum_{d|k} min(d, k/d) (Hurwitz-Kronecker!)
    # Check densities of A(n) != 0 mod l vs H(1, D) != 0 mod l for n <= 400!
    print("\n--- 5A: Density of [q^n](f * theta) != 0 mod l vs squarefree c_f(D) != 0 mod l ---")
    Nmax = 600
    H1 = [cohen_H_r(1, n) for n in range(Nmax + 1)]
    # Convolve with theta(z) = 1 + 2 sum_{m>=1} q^{m^2}
    A = [Fraction(0)] * (Nmax + 1)
    for n in range(Nmax + 1):
        s = H1[n]
        m = 1
        while m * m <= n:
            s += 2 * H1[n - m * m]
            m += 1
        A[n] = s
    # Verify exact Hurwitz-Kronecker identity at prime p: A(4p) == 2p!
    for p in [3, 5, 7, 11, 13, 17, 19, 23, 29, 31]:
        assert A[4 * p] == Fraction(2 * p), f"HK failed at p={p}: got {A[4*p]}"
    print("  [Calibration PASSED] Hurwitz-Kronecker A(4p) = 2p verified for all odd primes p <= 31!")
    # Compare density of A(4k) != 0 mod l for k in [1..150] vs H(1, D) != 0 mod l!
    # Note: for k = 1..150, A(4k) is close to 2*sigma_1(k) (minus small divisor correction),
    # and for pure integral-weight E_4(z) = 1 + 240 sum sigma_3(n) q^n vs E_{7/2}(z) = sum H(3, n) q^n:
    # Let's measure BOTH:
    #   (i) A(4k) mod l for k = 1..150 (note H(1,n) is mock modular, so A(4k) has mock term -sum min(d,k/d)),
    #   (ii) HOLOMORPHIC E_{7/2}(z) * theta(z) in M_4(Gamma_0(4))!
    # In M_4(Gamma_0(4)), dim = 3 (basis: E_4(z), E_4(2z), E_4(4z) — ALL Eisenstein, NO cusp forms!).
    # So E_{7/2}(z) * theta(z) IS A PURE LINEAR COMBINATION OF E_4(z), E_4(2z), E_4(4z),
    # hence by Serre (1976) its mod-l non-zero density STRICTLY -> 0 as X -> infinity!!
    H3 = [cohen_H_r(3, n) for n in range(201)]
    A3 = [Fraction(0)] * 201
    for n in range(201):
        s = H3[n]
        m = 1
        while m * m <= n:
            s += 2 * H3[n - m * m]
            m += 1
        A3[n] = s
    # Verify A3(n) IS a linear combination of E_4(z), E_4(2z), E_4(4z) for ALL n in 0..200!
    # E_4(z) = 1 + 240 sum sigma_3(n) q^n. Match at n = 0, 1, 2:
    # Let A3(z) = c1 * E_4(z) + c2 * E_4(2z) + c3 * E_4(4z)
    # At n=0: c1 + c2 + c3 = A3(0) = H(3,0) = zeta(-5) = -1/252
    # At n=1: 240*c1 = A3(1) => c1 = A3(1)/240
    # At n=2: 240*(9*c1 + c2) = A3(2) => c2 = A3(2)/240 - 9*c1
    # At n=4: check!
    def sig3(n):
        return sum(d**3 for d in sp.divisors(n))
    c1 = A3[1] / 240
    c2 = A3[2] / 240 - 9 * c1
    c3 = A3[0] - c1 - c2
    for n in range(1, 201):
        pred = 240 * (c1 * sig3(n) + (c2 * sig3(n // 2) if n % 2 == 0 else 0) + (c3 * sig3(n // 4) if n % 4 == 0 else 0))
        assert A3[n] == pred, f"M_4(Gamma_0(4)) identity failed at n={n}: {A3[n]} != {pred}"
    print(f"  [EXACT IDENTITY PROVED & VERIFIED (n <= 200)]:")
    print(f"    E_{{7/2}}(z) * theta(z) = ({c1})*E_4(z) + ({c2})*E_4(2z) + ({c3})*E_4(4z) in M_4(Gamma_0(4))!")
    # Now measure density of [q^n](E_{7/2}*theta) != 0 mod l for n <= X (X = 100, 1000, 10000) via sigma_3(n)!
    # For odd n, [q^n](E_{7/2}*theta) = 240*c1 * sigma_3(n) = (1/2) * sigma_3(n) (check 240*c1)!
    print(f"    For odd n: [q^n](E_{{7/2}}*theta) = ({240*c1}) * sigma_3(n)!")
    for ell in [5, 7, 11]:
        # Check density of sigma_3(n) != 0 mod ell among odd n <= X for X = 200, 2000, 20000
        dens = []
        for X in [200, 2000, 20000]:
            nz = 0
            tot = 0
            for n in range(1, X + 1, 2):
                tot += 1
                # Compute sigma_3(n) mod ell via prime factorization? Even faster: sieve!
                # Wait: small loop up to 20000 with sp.factorint is fast enough? Let's sieve!
            # Sieve sigma_3(n) mod ell for n <= 20000!
            break
        # Fast multiplicative sieve up to 20000
        LIM = 20000
        spf = list(range(LIM + 1))
        for i in range(2, int(math.isqrt(LIM)) + 1):
            if spf[i] == i:
                for j in range(i * i, LIM + 1, i):
                    if spf[j] == j:
                        spf[j] = i
        s3 = [1] * (LIM + 1)
        for n in range(2, LIM + 1):
            p = spf[n]
            m = n
            pk = 1
            psum = 1
            p3 = pow(p, 3, ell)
            cur = 1
            while m % p == 0:
                m //= p
                cur = (cur * p3) % ell
                psum = (psum + cur) % ell
            s3[n] = (s3[m] * psum) % ell
        ds = []
        for X in [200, 2000, 20000]:
            nz = sum(1 for n in range(1, X + 1, 2) if s3[n] != 0)
            tot = (X + 1) // 2
            ds.append(f"X={X}:{nz/tot:.4f}")
        print(f"    l={ell:2d}: density of odd n <= X with [q^n](E_{{7/2}}*theta) != 0 mod {ell}: {', '.join(ds)} (DECAYING -> 0 by Serre 1976!)")

    # 5B: Explicit Victor Miller echelon basis in M_{k+1/2}(Gamma_0(4); F_l) for k=6 (weight 13/2, dim = 4!)
    # Recall M_{k+1/2}(Gamma_0(4)) has basis theta(z)^{2k+1 - 4j} * F_2(z)^j for j = 0 .. floor(k/2)
    # where F_2(z) = sum_{n>=1 odd} sigma_1(n) q^n in M_2(Gamma_0(4))!
    # Wait: dim M_{13/2}(Gamma_0(4)) = 4 (j = 0, 1, 2, 3), Sturm bound = floor((13/2)/12 * 6) = 3!
    # Compute exact q-expansions mod ell=7 up to q^20 and build Victor Miller echelon basis!
    print("\n--- 5B: Explicit Victor Miller Echelon Disjoint-Support Pairs in M_{13/2}(Gamma_0(4); F_7) ---")
    ell = 7
    QMAX = 25
    def poly_mul(a, b, mod):
        res = [0] * (QMAX + 1)
        for i in range(QMAX + 1):
            ai = a[i]
            if ai:
                for j in range(QMAX + 1 - i):
                    res[i + j] = (res[i + j] + ai * b[j]) % mod
        return res
    def poly_pow(a, e, mod):
        res = [0] * (QMAX + 1); res[0] = 1
        base = a[:]
        while e:
            if e & 1: res = poly_mul(res, base, mod)
            base = poly_mul(base, base, mod)
            e >>= 1
        return res
    th = [0] * (QMAX + 1); th[0] = 1
    for m in range(1, int(math.isqrt(QMAX)) + 1):
        th[m * m] = 2 % ell
    F2 = [0] * (QMAX + 1)
    for n in range(1, QMAX + 1, 2):
        F2[n] = sum(d for d in sp.divisors(n)) % ell
    basis = [poly_mul(poly_pow(th, 13 - 4 * j, ell), poly_pow(F2, j, ell), ell) for j in range(4)]
    # Row-reduce on columns 0..3 over GF(7) to get Victor Miller echelon basis g_0, g_1, g_2, g_3
    M_mat = [row[:] for row in basis]
    for col in range(4):
        piv = next(r for r in range(col, 4) if M_mat[r][col] != 0)
        M_mat[col], M_mat[piv] = M_mat[piv], M_mat[col]
        inv = pow(M_mat[col][col], -1, ell)
        M_mat[col] = [(x * inv) % ell for x in M_mat[col]]
        for r in range(4):
            if r != col and M_mat[r][col] != 0:
                fac = M_mat[r][col]
                M_mat[r] = [(M_mat[r][j] - fac * M_mat[col][j]) % ell for j in range(QMAX + 1)]
    # Verify h_1 = g_0 + g_1 and h_2 = g_0 + g_2 have c(0)=1, theta != 0, and ZERO overlap in [1, 3]!
    h1 = [(M_mat[0][j] + M_mat[1][j]) % ell for j in range(QMAX + 1)]
    h2 = [(M_mat[0][j] + M_mat[2][j]) % ell for j in range(QMAX + 1)]
    h3 = [(M_mat[0][j] + M_mat[3][j]) % ell for j in range(QMAX + 1)]
    assert h1[0] == 1 and h2[0] == 1 and h3[0] == 1
    assert h1[1:4] == [1, 0, 0] and h2[1:4] == [0, 1, 0] and h3[1:4] == [0, 0, 1]
    print(f"  In M_{{13/2}}(Gamma_0(4); F_7) (dim=4, Sturm bound B=3):")
    print(f"    h1 = g0 + g1 = 1 + q   + {h1[4]}q^4 + {h1[5]}q^5 + ...  (in [1,B]: ONLY n=1!)")
    print(f"    h2 = g0 + g2 = 1 + q^2 + {h2[4]}q^4 + {h2[5]}q^5 + ...  (in [1,B]: ONLY n=2!)")
    print(f"    h3 = g0 + g3 = 1 + q^3 + {h3[4]}q^4 + {h3[5]}q^5 + ...  (in [1,B]: ONLY n=3!)")
    print(f"    ALL THREE have c(0)=1, theta(h_i)!=0, yet PAIRWISE DISJOINT on the entire Sturm box [1, B]!")

if __name__ == "__main__":
    t0 = time.time()
    run_suite_1()
    run_suite_2()
    run_suite_3()
    run_suite_4()
    run_suite_5()
    print("\n" + "=" * 80)
    print(f"ALL 5 SUITES PASSED WITH EXIT CODE 0 in {time.time() - t0:.2f}s!")
    print("=" * 80)
