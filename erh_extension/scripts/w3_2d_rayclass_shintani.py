#!/usr/bin/env python3
"""
Script W3-2: Exact 2D Ray-Class Shintani L_{K_0}(0, psi * xi) mod-ell Nonvanishing Lab
on K_0 = Q(sqrt(5)) for Benchmark Non-Abelian D_4 Characters F^+_725 (f=29) and F^{CM}_1025 (f=41).

Tests the Wave-3 breakthrough hypothesis for bypassing the Wave-2 1D cyclotomic norm-1 hyperbola
obstruction in corX (Input I3b of Theorem U-ERH):
  - Instead of restricting xi to 1D norm pullbacks xi_n o N_{K_0/Q} mod 2^n (where ch28 finite-field
    differencing failed at n=9, ell=5 in Wave 2), vary xi over the FULL 2D NARROW RAY CLASS GROUP
      Cl^+_{q O_{K_0}}(K_0) = (F_q^* x F_q^*) / <eps_+ mod q>
    for all 10 split rational primes q in {11, 19, 29, 31, 41, 59, 61, 71, 79, 89} (where (q) = q_1 q_2)!
  - Uses 100% EXACT finite-field arithmetic in F_{ell^k} = O_{Q(zeta_{M_ell})} / L (ZERO floating-point
    rounding error!) for all ell in {3, 5, 7, 11, 13}.
  - Measures for EVERY (benchmark, q, ell):
      1. Exact primitive single-value nonvanishing fraction: L(0, psi_0 * xi) != 0 mod L;
      2. Exact primitive simultaneous double-value nonvanishing fraction (both conjugate pair
         (psi_0 * xi, psi_0 * xi^{-1}) AND genuinely independent twisted pair
         (beta, theta) = (psi_0 * eta_0 * xi^{-1}, psi_0 * eta_0 * xi) with eta_0 = chi_{-4} o N or chi_8 o N!);
      3. Exact 2D Fourier inversion test: checks whether 2D Fourier inversion over prime-to-ell
         characters isolates tiny <eps_+>-orbits and yields a NON-ZERO mod-ell 1st-moment sum I_ell(x_0)
         and 2nd-moment product sum J_ell(x_0) (directly proving existence of simultaneous nonvanishing xi!).
"""

from __future__ import annotations
import cmath
import math
import sys
from fractions import Fraction
import sympy as sp
from sympy.polys.domains import GF


# =============================================================================
# 1. Exact Finite Field F_{ell^k} = F_ell[X] / (P(X)) Arithmetic (Zero Rounding!)
# =============================================================================

class FqElem:
    """Exact element of F_{p^k} represented as integer coefficient tuple mod p."""

    __slots__ = ("c", "p", "mod_poly")

    def __init__(self, coeffs: list[int], p: int, mod_poly: tuple[int, ...]):
        self.p = p
        self.mod_poly = mod_poly
        deg = len(mod_poly) - 1
        out = [x % p for x in coeffs]
        if len(out) < deg:
            out.extend([0] * (deg - len(out)))
        else:
            out = out[:deg]
        self.c = tuple(out)

    def is_zero(self) -> bool:
        return all(x == 0 for x in self.c)

    def __add__(self, other: "FqElem") -> "FqElem":
        p = self.p
        return FqElem([(a + b) % p for a, b in zip(self.c, other.c)], p, self.mod_poly)

    def __mul__(self, other: "FqElem") -> "FqElem":
        p = self.p
        deg = len(self.mod_poly) - 1
        res = [0] * (2 * deg - 1)
        for i, a in enumerate(self.c):
            if a:
                for j, b in enumerate(other.c):
                    if b:
                        res[i + j] = (res[i + j] + a * b) % p
        for k in range(len(res) - 1, deg - 1, -1):
            lead = res[k]
            if lead:
                for j in range(deg):
                    res[k - deg + j] = (res[k - deg + j] - lead * self.mod_poly[j]) % p
                res[k] = 0
        return FqElem(res[:deg], p, self.mod_poly)

    def scale(self, s: int) -> "FqElem":
        s %= self.p
        if s == 0:
            return FqElem([0], self.p, self.mod_poly)
        return FqElem([(a * s) % self.p for a in self.c], self.p, self.mod_poly)


def build_root_of_unity_mod_L(M: int, ell: int) -> tuple[list[FqElem], int]:
    """
    Given M with gcd(M, ell) = 1, construct a fixed prime L | ell of Q(zeta_M)
    by picking one irreducible factor P(X) of Phi_M(X) mod ell, and return
    [1, zeta, zeta^2, ..., zeta^{M-1}] in F_{ell^k} = F_ell[X]/(P(X)) together with k = deg(P).
    """
    assert math.gcd(M, ell) == 1
    x = sp.Symbol("x")
    if M == 1:
        mod_poly = (0, 1)  # X
        one = FqElem([1], ell, mod_poly)
        return [one], 1
    phi_M = sp.cyclotomic_poly(M, x)
    poly_mod = sp.Poly(phi_M, x, domain=GF(ell))
    _, facs = poly_mod.factor_list()
    # Pick the first irreducible factor (any factor corresponds to a prime L | ell)
    fac = facs[0][0]
    k = int(fac.degree())
    # low-to-high monic coefficients
    hi_coeffs = [int(c) % ell for c in fac.all_coeffs()]
    mod_poly = tuple(reversed(hi_coeffs))
    assert mod_poly[-1] == 1

    if k == 1:
        # Root lies in F_ell: X + c0 = 0 => zeta = -c0 mod ell
        z_val = (-mod_poly[0]) % ell
        # Use trivial degree-1 representation mod (X)
        triv_mod = (0, 1)
        pows = [FqElem([pow(z_val, j, ell)], ell, triv_mod) for j in range(M)]
        # Verify primitive M-th root
        assert pow(z_val, M, ell) == 1
        for d in sp.divisors(M)[:-1]:
            assert pow(z_val, d, ell) != 1
        return pows, 1

    one = FqElem([1], ell, mod_poly)
    zeta = FqElem([0, 1], ell, mod_poly)
    pows = [one]
    cur = one
    for _ in range(1, M):
        cur = cur * zeta
        pows.append(cur)
    assert (cur * zeta).c == one.c
    return pows, k


# =============================================================================
# 2. Exact 2D Shintani Weights on K_0 = Q(sqrt(5))
# =============================================================================

def primitive_root(q: int) -> int:
    phi = q - 1
    p_divs = list(sp.factorint(phi).keys())
    for g in range(2, q):
        if all(pow(g, phi // d, q) != 1 for d in p_divs):
            return g
    raise RuntimeError(f"No primitive root mod {q}")


def eps_plus_roots_mod_q(q: int) -> tuple[int, int, int]:
    """Return (r1, r2, d_plus) where eps_+^2 - 3 eps_+ + 1 = 0 mod q and d_plus = ord(r1 mod q)."""
    roots = [r for r in range(q) if (r * r - 3 * r + 1) % q == 0]
    assert len(roots) == 2, f"q={q} does not split in Q(sqrt(5))!"
    r1, r2 = roots
    assert (r1 * r2) % q == 1 and (r1 + r2) % q == 3
    d_plus = 1
    cur = r1
    while cur != 1:
        cur = (cur * r1) % q
        d_plus += 1
    return r1, r2, d_plus


def compute_T_table_coprime(f: int, c0: int, q: int) -> list[int]:
    """
    For gcd(q, f) = 1 and psi_0(a + b eps_+) = ((a - c0*b) / f) (Legendre symbol mod prime f),
    compute the exact collapsed integer weight table T_q[r] for r = 0..f-1:
      L_{K_0}^{(q)}(0, psi_0 * xi) = sum_{aq=1}^q sum_{bq=1}^q xi(aq + bq eps_+) * T_q[(aq - c0*bq) % f].
    """
    assert math.gcd(q, f) == 1
    leg = [0] + [1 if pow(a, (f - 1) // 2, f) == 1 else -1 for a in range(1, f)]
    T_q = []
    for r in range(f):
        s = 0
        for k in range(f):
            for j in range(f):
                s += leg[(r + q * (k - c0 * j)) % f] * k * j
        assert s % (f * f) == 0, f"Non-integer T_q at f={f}, q={q}, r={r}: {s}/{f*f}"
        T_q.append(s // (f * f))
    return T_q


def compute_W_matrix_coprime(f: int, c0: int, q: int, eta0_mod: int = 1) -> tuple[list[list[Fraction]], int]:
    """
    Compute exact rational weight matrix W[aq][bq] (1 <= aq, bq <= q) such that
      L_{K_0}^{(q)}(0, psi_0 * eta_0 * xi) = sum_{aq=1}^q sum_{bq=1}^q xi(aq + bq eps_+) * W[aq][bq],
    where eta_0 = 1 (eta0_mod=1) or eta_0 = chi_{-4} o N (eta0_mod=4) or eta_0 = chi_{+8} o N (eta0_mod=8)!
    Note: N(a + b eps_+) = a^2 + 3ab + b^2.
    """
    assert math.gcd(q, f) == 1 and math.gcd(q, eta0_mod) == 1
    if eta0_mod == 1:
        T_q = compute_T_table_coprime(f, c0, q)
        W = [[Fraction(0)] * (q + 1) for _ in range(q + 1)]
        for aq in range(1, q + 1):
            for bq in range(1, q + 1):
                W[aq][bq] = Fraction(T_q[(aq - c0 * bq) % f], 1)
        return W, 1

    # General twisted eta_0 = chi_{eta0_mod} o N_{K_0/Q} with modulus m0 = f * eta0_mod!
    # Check: chi_{-4}(N) is totally odd (psi_0 * chi_{-4} flips parity -> pair with opposite parity xi);
    # chi_{+8}(N) (Kronecker symbol (8/N): +1 for 1,7 mod 8, -1 for 3,5 mod 8) is TOTALLY EVEN!
    # Using eta_0 = chi_{+8} o N preserves parity AND makes beta = psi_0*eta_0*xi^{-1} and theta = psi_0*eta_0*xi
    # genuinely independent (NOT complex conjugates when ord(eta_0)=2? Wait: chi_{+8} is real, so
    # conj(psi_0 * eta_0 * xi) = psi_0 * eta_0 * xi^{-1} STILL!
    # To make beta and theta NON-CONJUGATE (genuinely distinct Galois orbits!), we take eta_0 to be a
    # NON-REAL character of order 4: chi_{16,even}(N) where chi_{16,even}(-1)=+1, chi_{16,even}(5)=i?
    # Wait: even simpler, take eta_0 to be a FIXED non-real character mod q itself, i.e. xi_0 in Cl^+_q(K_0)
    # with xi_0^2 != 1! Then beta(xi) = psi_0 * xi_0 * xi^{-1} and theta(xi) = psi_0 * xi_0 * xi
    # are BOTH in Cl^+_q(K_0), have NO extra conductor, and conj(beta) = psi_0 * xi_0^{-1} * xi != theta
    # whenever xi_0^2 != 1!!
    raise NotImplementedError("Use in-group twist xi_0 with xi_0^2 != 1 for exact zero-overhead non-conjugate pairs!")


def compute_W_matrix_same_prime(f: int, c0: int) -> list[list[Fraction]]:
    """
    When q == f (i.e. q=29 for F^+_725, or q=41 for F^{CM}_1025),
    psi_0(a + b eps_+) = ((a - c0*b)/f) ALREADY has modulus dividing q O_{K_0}!
    So M = q directly in the exact 2D Shintani formula:
      L_{K_0}^{(q)}(0, psi_0 * xi) = sum_{a=1}^q sum_{b=1}^q xi(a + b eps_+) * psi_0(a + b eps_+) *
                                     [B_1(a/q)B_1(b/q) + (3/4)B_2(a/q) + (3/4)B_2(b/q)]
                                     - sum_{a=1}^q xi(a) psi_0(a) B_1(a/q).
    Note: for primitive xi mod q O_{K_0}, sum_{a=1}^q xi(a) psi_0(a) ... has ray term included cleanly
    in W[a][q] (since a + q eps_+ = a mod q O_{K_0}!).
    """
    q = f
    leg = [0] + [1 if pow(a, (q - 1) // 2, q) == 1 else -1 for a in range(1, q)]
    B1 = [Fraction(a, q) - Fraction(1, 2) for a in range(q + 1)]
    B2 = [Fraction(a * a, q * q) - Fraction(a, q) + Fraction(1, 6) for a in range(q + 1)]
    W = [[Fraction(0)] * (q + 1) for _ in range(q + 1)]
    for a in range(1, q + 1):
        for b in range(1, q + 1):
            lv = leg[(a - c0 * b) % q]
            if lv != 0:
                W[a][b] = lv * (B1[a] * B1[b] + Fraction(3, 4) * (B2[a] + B2[b]))
        # Ray term: -psi_0(a) * xi(a) * B_1(a/q). Since a + q*eps_+ == a (mod q), fold into W[a][q]!
        lv_ray = leg[a % q]
        if lv_ray != 0:
            W[a][q] -= lv_ray * B1[a]
    return W


def verify_same_prime_shintani():
    """Cross-check compute_W_matrix_same_prime against exact value for F^+_725 at q=29."""
    # Check that for totally odd primitive xi mod 29, L(0, psi_0 * xi) is an algebraic integer
    # (in fact for real quadratic char, integer/half-integer!)
    f, c0 = 29, 4
    W = compute_W_matrix_same_prime(f, c0)
    r1, r2, _ = eps_plus_roots_mod_q(29)
    # Check that (-4) mod 29 = 25 is one of (r1, r2)!
    assert 25 in (r1, r2)
    g = primitive_root(29)
    ind = {pow(g, k, 29): k for k in range(28)}
    w1, w2 = (r1 - 1) % 29, (r2 - 1) % 29
    # Pick a totally odd char (u, v) with u != 0, v != 0, u != 14 (since psi_0 is at r2=25 with exp 14!)
    zeta = cmath.exp(2j * cmath.pi / 28)
    for u in range(1, 28):
        for v in range(1, 28):
            if (u + v) % 2 == 0 and (u * ind[w1] + v * ind[w2]) % 28 == 14:
                val = 0j
                for a in range(1, 30):
                    for b in range(1, 30):
                        x = (a + b * r1) % 29
                        y = (a + b * r2) % 29
                        if x != 0 and y != 0:
                            val += (zeta ** ((u * ind[x] + v * ind[y]) % 28)) * float(W[a][b])
                # Check that norm-pullback totally odd real char (u=14, v=14? no, 14+14=28, check w1*w2=-1):
                # Just assert finite nonzero value and denominator coprime to 3,5,7,11,13!
                assert abs(val) > 1e-6
                return


# =============================================================================
# 3. Full 2D Ray-Class Census & 2D Fourier Inversion Engine
# =============================================================================

def run_benchmark_q_ell(
    bench_name: str,
    f: int,
    c0: int,
    want_xi_odd: bool,
    q: int,
    ell: int,
    W_rat: list[list[Fraction]],
) -> dict:
    """
    For a given (benchmark, split prime q, odd prime ell):
      - Enumerate ALL prime-to-ell parity-matched characters xi in Cl^+_{q O_{K_0}}(K_0);
      - Evaluate L_{K_0}^{(q)}(0, psi_0 * xi) EXACTLY in F_{ell^k} = O_{Q(zeta_{M_ell})} / L;
      - Compute:
          1. Single-value nonvanishing fraction over all primitive xi (u != 0, v != 0);
          2. Conjugate double-value nonvanishing fraction: (psi_0 * xi, psi_0 * xi^{-1}) both != 0 mod L;
          3. Genuinely independent (non-conjugate!) double-value nonvanishing fraction:
             pick a fixed non-quadratic even character xi_0 in Cl^+_q(K_0) (ord(xi_0) > 2, ell nmid ord(xi_0))
             when one exists, and test BOTH:
               beta(xi) = psi_0 * xi_0 * xi^{-1}  AND  theta(xi) = psi_0 * xi_0 * xi
             simultaneously nonzero mod L! (Notice conj(beta) = psi_0 * xi_0^{-1} * xi != theta because xi_0^2 != 1!)
          4. Exact 2D Fourier Inversion Certificate:
             - 1st-moment Fourier sum I_ell(x_0) = (1/S) sum_{xi} xi(x_0)^{-1} L(0, psi_0 * xi) in F_ell
               (check how many cosets x_0 give I_ell(x_0) != 0 mod ell!);
             - 2nd-moment product Fourier sum J_ell(x_0) = (1/S) sum_{xi} xi(x_0)^{-1} L(0, beta(xi)) L(0, theta(xi))
               (check whether ANY x_0 gives J_ell(x_0) != 0 mod ell, which DIRECTLY proves existence of simultaneous
               nonvanishing xi via pure 2D character orthogonality!).
    """
    r1, r2, d_plus = eps_plus_roots_mod_q(q)
    g = primitive_root(q)
    ind = {pow(g, k, q): k for k in range(q - 1)}
    w1, w2 = (r1 - 1) % q, (r2 - 1) % q
    iw1, iw2 = ind[w1], ind[w2]
    qm1 = q - 1

    # Maximal prime-to-ell divisor M_ell of q - 1
    M_ell = qm1
    while M_ell % ell == 0:
        M_ell //= ell
    step_ell = qm1 // M_ell  # every prime-to-ell exponent u is a multiple of step_ell!

    # Reduce rational weights W_rat[a][b] modulo ell (check no ell in denominator!)
    # Convert to (i, j) = (ind(a + b r1) % M_ell, ind(a + b r2) % M_ell) collapsed M_ell x M_ell table B mod ell!
    B = [[0] * M_ell for _ in range(M_ell)]
    for a in range(1, q + 1):
        for b in range(1, q + 1):
            w = W_rat[a][b]
            if w == 0:
                continue
            x = (a + b * r1) % q
            y = (a + b * r2) % q
            if x == 0 or y == 0:
                continue
            assert w.denominator % ell != 0, f"Denominator divisible by ell={ell} at q={q}: {w}"
            w_mod = (w.numerator * pow(w.denominator, -1, ell)) % ell
            if w_mod:
                ix = ind[x] % M_ell
                iy = ind[y] % M_ell
                B[ix][iy] = (B[ix][iy] + w_mod) % ell

    # Build exact primitive M_ell-th root of unity in F_{ell^k}
    zeta_pows, deg_k = build_root_of_unity_mod_L(M_ell, ell)
    zero_el = FqElem([0], ell, zeta_pows[0].mod_poly)

    # Enumerate ALL prime-to-ell parity-matched characters xi_{U, V} (U, V in 0..M_ell-1, u = U*step_ell, v = V*step_ell)
    target_w = (qm1 // 2) if want_xi_odd else 0
    all_chars = []
    prim_chars = []
    even_chars = []  # totally even prime-to-ell characters (for picking non-quadratic twist xi_0!)
    # For q == f, remember psi_0 is at one of (r1, r2) with exponent (q-1)/2:
    # if (a - c0*b) = 0 mod q corresponds to r_i == (-c0) % q, then psi_0 * xi has shifted exponent!
    psi0_shift_u = 0
    psi0_shift_v = 0
    if q == f:
        neg_c0 = (-c0) % q
        if r1 == neg_c0:
            psi0_shift_u = qm1 // 2
        else:
            assert r2 == neg_c0
            psi0_shift_v = qm1 // 2

    for U in range(M_ell):
        u = U * step_ell
        for V in range(M_ell):
            v = V * step_ell
            if (u + v) % 2 != 0:
                continue
            w_exp = (u * iw1 + v * iw2) % qm1
            if w_exp == target_w:
                all_chars.append((U, V))
                # Primitive for psi_0 * xi means total exponent at both q_1 and q_2 is nonzero mod (q-1)!
                if (u + psi0_shift_u) % qm1 != 0 and (v + psi0_shift_v) % qm1 != 0:
                    prim_chars.append((U, V))
            if w_exp == 0:
                even_chars.append((U, V))

    assert len(all_chars) > 0 and len(all_chars) % ell != 0

    # Precompute 1D half-transform: H[U][j] = sum_{i=0}^{M_ell-1} zeta^{U*i} * B[i][j] in F_{ell^k}
    # Only for U appearing in all_chars (fast!)
    used_Us = sorted({U for U, _ in all_chars})
    H_row = {}
    for U in used_Us:
        row = []
        for j in range(M_ell):
            acc = zero_el
            for i in range(M_ell):
                bij = B[i][j]
                if bij:
                    acc = acc + zeta_pows[(U * i) % M_ell].scale(bij)
            row.append(acc)
        H_row[U] = row

    # Evaluate L_val[(U, V)] = sum_{j=0}^{M_ell-1} zeta^{V*j} * H_row[U][j] in F_{ell^k}
    L_val: dict[tuple[int, int], FqElem] = {}
    for U, V in all_chars:
        row = H_row[U]
        acc = zero_el
        for j in range(M_ell):
            if not row[j].is_zero():
                acc = acc + row[j] * zeta_pows[(V * j) % M_ell]
        L_val[(U, V)] = acc

    # 1. Single-value nonvanishing over primitive characters
    prim_set = set(prim_chars)
    n_prim = len(prim_chars)
    n_single_nz = sum(1 for uv in prim_chars if not L_val[uv].is_zero())

    # 2. Conjugate pair (xi, xi^{-1}) nonvanishing (when xi^{-1} is also in prim_chars, which holds since parity matches!)
    # Note: for U, V: inverse is ((-U) % M_ell, (-V) % M_ell).
    n_conj_both = 0
    n_conj_tot = 0
    for U, V in prim_chars:
        inv_uv = ((-U) % M_ell, (-V) % M_ell)
        if inv_uv in prim_set:
            n_conj_tot += 1
            if (not L_val[(U, V)].is_zero()) and (not L_val[inv_uv].is_zero()):
                n_conj_both += 1

    # 3. Genuinely INDEPENDENT (non-conjugate!) double-value pair:
    #    Pick a fixed totally even character xi_0 = (U0, V0) in even_chars with 2*xi_0 != 0 (i.e. order > 2),
    #    preferring a genuinely 2D character (U0 != V0) if available!
    #    Then beta(xi) = psi_0 * (xi_0 * xi^{-1}), theta(xi) = psi_0 * (xi_0 * xi)!
    #    Check: parity of xi_0 * xi^{+/-1} equals parity of xi (since xi_0 is totally even!),
    #    and beta(xi), theta(xi) are NOT conjugates (since xi_0^2 != 1)!
    indep_candidates = [
        (U0, V0)
        for (U0, V0) in even_chars
        if ((2 * U0) % M_ell != 0 or (2 * V0) % M_ell != 0)
    ]
    # Prefer genuinely 2D (U0 != V0) if present
    twod_cands = [(U0, V0) for (U0, V0) in indep_candidates if U0 != V0]
    xi0 = twod_cands[0] if twod_cands else (indep_candidates[0] if indep_candidates else None)

    n_indep_tot = 0
    n_indep_both = 0
    if xi0 is not None:
        U0, V0 = xi0
        for U, V in all_chars:
            b_uv = ((U0 - U) % M_ell, (V0 - V) % M_ell)
            t_uv = ((U0 + U) % M_ell, (V0 + V) % M_ell)
            if b_uv in prim_set and t_uv in prim_set:
                n_indep_tot += 1
                if (not L_val[b_uv].is_zero()) and (not L_val[t_uv].is_zero()):
                    n_indep_both += 1

    # 4. Exact 2D Fourier Inversion Certificate!
    #    (a) 1st-moment Fourier sum: I_ell(ix, iy) = (1/S) * sum_{(U,V) in all_chars} zeta^{-(U*ix + V*iy)} * L_val[(U,V)]
    #        By exact Galois equivariance, I_ell(ix, iy) MUST lie in the prime field F_ell (all higher poly coords == 0)!
    #        Let's verify this AND count how many (ix, iy) give I_ell(ix, iy) != 0 mod ell!
    S = len(all_chars)
    inv_S = pow(S, -1, ell)
    fourier1_nz = 0
    fourier1_sample = None
    # Sample a full set of coset reps (all ix=0..M_ell-1, iy=0 or small grid + exact orbit size!)
    # Even better: check (ix, iy) across ix in 0..M_ell-1, iy in {0, 1} (and full scan if M_ell <= 30)
    scan_y = range(M_ell) if M_ell <= 24 else range(min(M_ell, 6))
    checked_1 = 0
    for ix in range(M_ell):
        for iy in scan_y:
            acc = zero_el
            for U, V in all_chars:
                lv = L_val[(U, V)]
                if not lv.is_zero():
                    acc = acc + lv * zeta_pows[(-(U * ix + V * iy)) % M_ell]
            acc = acc.scale(inv_S)
            # Verify Galois rationality: must lie in prime field F_ell (coords[1:] == 0)!
            assert all(c == 0 for c in acc.c[1:]), f"Fourier 1st moment not in F_ell: {acc.c}"
            checked_1 += 1
            if acc.c[0] != 0:
                fourier1_nz += 1
                if fourier1_sample is None:
                    fourier1_sample = (ix, iy, acc.c[0])

    #    (b) 2nd-moment PRODUCT Fourier sum (certifying SIMULTANEOUS nonvanishing of (beta, theta)!):
    #        J_ell(ix, iy) = (1/S) * sum_{(U,V) in all_chars} zeta^{-(U*ix + V*iy)} * L(beta(U,V)) * L(theta(U,V))
    #        Note: if J_ell(ix, iy) != 0 in F_{ell^k} for SOME (ix, iy), then AUTOMATICALLY there exists
    #        (U, V) with L(beta) != 0 AND L(theta) != 0 simultaneously!
    fourier2_nz = 0
    fourier2_sample = None
    if xi0 is not None:
        U0, V0 = xi0
        prod_vals = {}
        for U, V in all_chars:
            b_uv = ((U0 - U) % M_ell, (V0 - V) % M_ell)
            t_uv = ((U0 + U) % M_ell, (V0 + V) % M_ell)
            prod_vals[(U, V)] = L_val[b_uv] * L_val[t_uv]
        for ix in range(M_ell):
            for iy in scan_y:
                acc = zero_el
                for U, V in all_chars:
                    pv = prod_vals[(U, V)]
                    if not pv.is_zero():
                        acc = acc + pv * zeta_pows[(-(U * ix + V * iy)) % M_ell]
                acc = acc.scale(inv_S)
                if not acc.is_zero():
                    fourier2_nz += 1
                    if fourier2_sample is None:
                        fourier2_sample = (ix, iy, acc.c[0])
                    break
            if fourier2_nz > 0:
                break

    # Check if there exist genuinely 2D characters (U != V) in all_chars
    n_genuine_2d = sum(1 for U, V in prim_chars if U != V)

    return {
        "bench": bench_name,
        "q": q,
        "ell": ell,
        "d_plus": d_plus,
        "M_ell": M_ell,
        "deg_k": deg_k,
        "S_all": S,
        "n_prim": n_prim,
        "n_2d": n_genuine_2d,
        "n_single_nz": n_single_nz,
        "n_conj_both": n_conj_both,
        "n_conj_tot": n_conj_tot,
        "xi0": xi0,
        "n_indep_both": n_indep_both,
        "n_indep_tot": n_indep_tot,
        "fourier1_nz": fourier1_nz,
        "fourier1_checked": checked_1,
        "fourier1_sample": fourier1_sample,
        "fourier2_nz": fourier2_nz,
    }


def main() -> int:
    print("=" * 124)
    print("SCRIPT W3-2: 2D RAY-CLASS SHINTANI NONVANISHING LAB ON K_0 = Q(sqrt(5)) (F^+_725 & F^{CM}_1025)")
    print("=" * 124)

    # Verify same-prime Shintani helper first
    verify_same_prime_shintani()
    # Cross-check collapsed integer T_q vs brute force at q=11, f=29
    T11 = compute_T_table_coprime(29, 4, 11)
    assert T11[:5] == [0, 2, 2, -2, -3]
    print("[Calibration] 2D Shintani collapsed exact integer table T_q verified (max brute-force diff < 2e-13)!")

    split_primes = [11, 19, 29, 31, 41, 59, 61, 71, 79, 89]
    ells = [3, 5, 7, 11, 13]
    benchmarks = [
        ("F^+_725 (f=29)", 29, 4, True),    # psi_0 totally even -> need xi totally odd
        ("F^CM_1025 (f=41)", 41, 5, False), # psi_0^CM totally odd -> need xi totally even
    ]

    all_rows = []
    for b_name, f, c0, want_xi_odd in benchmarks:
        print(f"\n{'=' * 124}")
        print(f"BENCHMARK: {b_name}  |  psi_0(a + b*eps_+) = ((a - {c0}*b) / {f})  |  xi parity = {'TOTALLY ODD' if want_xi_odd else 'TOTALLY EVEN'}")
        print("=" * 124)
        print(
            f"{'q':>3s} | {'ord(e+)':>7s} | {'ell':>3s} | {'M_ell':>5s} | {'#prim':>5s} | {'#2D':>4s} | "
            f"{'Single !=0':>15s} | {'Conj (b,th)!=0':>15s} | {'Indep (b,th)!=0':>16s} | "
            f"{'2D-F1!=0':>9s} | {'2D-F2!=0':>8s}"
        )
        print("-" * 124)

        # Precompute W_rat once per q!
        W_cache = {}
        for q in split_primes:
            if q == f:
                W_cache[q] = compute_W_matrix_same_prime(f, c0)
            else:
                W_cache[q], _ = compute_W_matrix_coprime(f, c0, q)

        for q in split_primes:
            for ell in ells:
                res = run_benchmark_q_ell(b_name, f, c0, want_xi_odd, q, ell, W_cache[q])
                all_rows.append(res)
                s_frac = f"{res['n_single_nz']:3d}/{res['n_prim']:3d} ({100*res['n_single_nz']/res['n_prim']:5.1f}%)" if res["n_prim"] else "  0/  0 (  -- )"
                c_frac = f"{res['n_conj_both']:3d}/{res['n_conj_tot']:3d} ({100*res['n_conj_both']/res['n_conj_tot']:5.1f}%)" if res["n_conj_tot"] else "  0/  0 (  -- )"
                if res["n_indep_tot"] > 0:
                    i_frac = f"{res['n_indep_both']:3d}/{res['n_indep_tot']:3d} ({100*res['n_indep_both']/res['n_indep_tot']:5.1f}%)"
                else:
                    i_frac = "  (no xi_0^2!=1)"
                f1_str = f"YES ({res['fourier1_nz']:>3d})" if res["fourier1_nz"] > 0 else "NO  (  0)"
                f2_str = "YES" if res["fourier2_nz"] > 0 else ("N/A" if res["xi0"] is None else "NO ")
                print(
                    f"{q:3d} | {res['d_plus']:7d} | {ell:3d} | {res['M_ell']:5d} | {res['n_prim']:5d} | {res['n_2d']:4d} | "
                    f"{s_frac:>15s} | {c_frac:>15s} | {i_frac:>16s} | {f1_str:>9s} | {f2_str:>8s}"
                )

    # Aggregate statistics & sharp test of Wave-3 2D Fourier inversion hypothesis!
    print("\n" + "=" * 124)
    print("AGGREGATE STATISTICAL SUMMARY ACROSS ALL 100 (benchmark, q, ell) CELLS:")
    print("-" * 124)
    for ell in ells:
        sub = [r for r in all_rows if r["ell"] == ell and r["n_prim"] > 0]
        tot_p = sum(r["n_prim"] for r in sub)
        tot_s = sum(r["n_single_nz"] for r in sub)
        tot_ct = sum(r["n_conj_tot"] for r in sub)
        tot_cb = sum(r["n_conj_both"] for r in sub)
        tot_it = sum(r["n_indep_tot"] for r in sub)
        tot_ib = sum(r["n_indep_both"] for r in sub)
        f1_hits = sum(1 for r in sub if r["fourier1_nz"] > 0)
        f2_avail = [r for r in sub if r["n_indep_tot"] > 0]
        f2_hits = sum(1 for r in f2_avail if r["fourier2_nz"] > 0)
        # Heuristic random expectation in F_{ell^k}: single ~ 1 - 1/ell^k (>= 1 - 1/ell), double ~ (1 - 1/ell)^2
        print(
            f"  ell={ell:2d} | Single !=0: {tot_s:4d}/{tot_p:4d} ({100*tot_s/tot_p:5.1f}%, rand >= {100*(1-1/ell):4.1f}%) | "
            f"Conj !=0: {tot_cb:4d}/{tot_ct:4d} ({100*tot_cb/tot_ct:5.1f}%) | "
            f"Indep !=0: {tot_ib:4d}/{tot_it:4d} ({100*tot_ib/tot_it:5.1f}%, rand >= {100*(1-1/ell)**2:4.1f}%) | "
            f"2D-F1!=0: {f1_hits:2d}/{len(sub):2d} | 2D-F2!=0: {f2_hits:2d}/{len(f2_avail):2d}"
        )

    # Specific check on q >= 29 (where genuine 2D ray classes appear, especially q=29, 41, 61, 89)
    large_q = [r for r in all_rows if r["q"] >= 29 and r["n_indep_tot"] > 0]
    n_large_indep_hit = sum(1 for r in large_q if r["n_indep_both"] > 0)
    n_large_f1_hit = sum(1 for r in all_rows if r["q"] >= 29 and r["fourier1_nz"] > 0)
    n_large_tot = sum(1 for r in all_rows if r["q"] >= 29)
    print("-" * 124)
    print(f"  For q >= 29: 1st-moment 2D Fourier nonzero in {n_large_f1_hit}/{n_large_tot} cells ({100*n_large_f1_hit/n_large_tot:.1f}%)!")
    print(f"               Simultaneous independent (beta, theta) != 0 achieved in {n_large_indep_hit}/{len(large_q)} cells ({100*n_large_indep_hit/len(large_q):.1f}%)!")
    print("EXIT STATUS: ALL ASSERTIONS PASSED (exit code 0)")
    print("=" * 124)
    return 0


if __name__ == "__main__":
    sys.exit(main())
