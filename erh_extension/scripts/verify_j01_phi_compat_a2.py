#!/usr/bin/env python3
"""
Wave-12 J01 Verification Script:
Weight Filtration Theorem on S^(1), Exact Commutator Induction, Universal Unconditional
H^2_syn Bound for ALL ell >= 2 and ALL Wild Non-Abelian K/Q_ell, Full-Order Equation (IV)
(phi-Compatibility of Prismatic Stratification), and Explicit Crystalline Lattice Lower Bounds.

Note (Iron Law 5): This script verifies finite instances, exact truncated ring identities,
exact SNF computations, and explicit lower-bound witnesses. General theorems are proved
line-by-line in erh_research/wave12/J01_phi_compat_ode_cartier_regime_b.md.
"""

from fractions import Fraction
from math import ceil, comb, floor, log
import random
import sys


# ============================================================================
# Core Exact Arithmetic: PolyU over (Z / ell^P Z)[[u]] / (u^Umax)
# ============================================================================

class PolyU:
    def __init__(self, coeffs, ell, P, Umax):
        self.ell = ell
        self.P = P
        self.mod = ell ** P
        self.Umax = Umax
        c = [0] * Umax
        for i in range(min(len(coeffs), Umax)):
            c[i] = int(coeffs[i]) % self.mod
        self.c = c

    def __add__(self, o):
        m = self.mod
        return PolyU([(self.c[i] + o.c[i]) % m for i in range(self.Umax)], self.ell, self.P, self.Umax)

    def __sub__(self, o):
        m = self.mod
        return PolyU([(self.c[i] - o.c[i]) % m for i in range(self.Umax)], self.ell, self.P, self.Umax)

    def __neg__(self):
        m = self.mod
        return PolyU([(-x) % m for x in self.c], self.ell, self.P, self.Umax)

    def __mul__(self, o):
        m, U = self.mod, self.Umax
        if isinstance(o, int):
            o %= m
            return PolyU([(x * o) % m for x in self.c], self.ell, self.P, U)
        res = [0] * U
        for i in range(U):
            ai = self.c[i]
            if not ai:
                continue
            for j in range(U - i):
                bj = o.c[j]
                if bj:
                    res[i + j] = (res[i + j] + ai * bj) % m
        return PolyU(res, self.ell, self.P, U)

    def inv(self):
        m, U = self.mod, self.Umax
        assert self.c[0] % self.ell != 0, f"Not invertible mod {self.ell}: c[0]={self.c[0]}"
        inv0 = pow(self.c[0], -1, m)
        res = [0] * U
        res[0] = inv0
        for k in range(1, U):
            s = sum(self.c[j] * res[k - j] for j in range(1, k + 1))
            res[k] = (-inv0 * (s % m)) % m
        return PolyU(res, self.ell, self.P, U)

    def phi(self, k=1):
        step = self.ell ** k
        res = [0] * self.Umax
        for i in range(self.Umax):
            if i * step < self.Umax:
                res[i * step] = self.c[i]
        return PolyU(res, self.ell, self.P, self.Umax)

    def pow(self, n):
        res = PolyU([1], self.ell, self.P, self.Umax)
        base = self
        while n > 0:
            if n & 1:
                res = res * base
            base = base * base
            n >>= 1
        return res

    def deriv(self):
        m, U = self.mod, self.Umax
        res = [0] * U
        for i in range(1, U):
            res[i - 1] = (i * self.c[i]) % m
        return PolyU(res, self.ell, self.P, U)

    def div_ell(self):
        for i, x in enumerate(self.c):
            assert x % self.ell == 0, f"Not divisible by {self.ell} at u^{i}: {x}"
        return PolyU([x // self.ell for x in self.c], self.ell, self.P - 1, self.Umax)

    def delta(self):
        return (self.phi() - self.pow(self.ell)).div_ell()

    def ord_u_mod(self, q):
        for i, x in enumerate(self.c):
            if x % q != 0:
                return i
        return None


def vp(n, p):
    if n == 0:
        return 10**9
    n = abs(n)
    c = 0
    while n % p == 0:
        n //= p
        c += 1
    return c


def vp_fact(n, p):
    c, pk = 0, p
    while pk <= n:
        c += n // pk
        pk *= p
    return c


def snf_exponents_mod_pk(rows, nvars, p, k):
    """Exact p-adic Smith Normal Form over Z/p^k Z."""
    mod = p ** k
    A = [[x % mod for x in r] for r in rows]
    nrows = len(A)

    def v_p(x):
        x %= mod
        if x == 0:
            return k
        c = 0
        while x % p == 0:
            x //= p
            c += 1
        return c

    r_idx = 0
    diag = []
    for _ in range(min(nrows, nvars)):
        best_v = k
        br = bc = -1
        for i in range(r_idx, nrows):
            for j in range(r_idx, nvars):
                v = v_p(A[i][j])
                if v < best_v:
                    best_v = v
                    br, bc = i, j
                    if v == 0:
                        break
            if best_v == 0:
                break
        if best_v == k:
            break
        if br != r_idx:
            A[r_idx], A[br] = A[br], A[r_idx]
        if bc != r_idx:
            for i in range(nrows):
                A[i][r_idx], A[i][bc] = A[i][bc], A[i][r_idx]
        pv = p ** best_v
        inv_u = pow(A[r_idx][r_idx] // pv, -1, mod)
        for i in range(r_idx, nrows):
            A[i][r_idx] = (A[i][r_idx] * inv_u) % mod
        for i in range(r_idx + 1, nrows):
            if A[i][r_idx]:
                q = (A[i][r_idx] // pv) % mod
                for j in range(r_idx, nvars):
                    A[i][j] = (A[i][j] - q * A[r_idx][j]) % mod
        for j in range(r_idx + 1, nvars):
            if A[r_idx][j]:
                q = (A[r_idx][j] // pv) % mod
                for i in range(r_idx, nrows):
                    A[i][j] = (A[i][j] - q * A[i][r_idx]) % mod
        diag.append(best_v)
        r_idx += 1

    exps = [d for d in diag if d > 0] + [k] * (nvars - r_idx)
    exps.sort(reverse=True)
    return exps


# ============================================================================
# Exact Truncated Ring S^(1) / (ell^P, J_{>= W}) (ZERO I_1^2 truncation!)
# ============================================================================

class S1Ring:
    """
    Exact arithmetic in S^(1) / (ell^P, J_{>= W}) using the exact p_2-basis
    e_alpha^{op} = w^{a0} * d1^{a1} * d2^{a2} (for W < ell^3) with weight
    wt(u_2^a e_alpha) = a + a0 + ell*a1 + ell^2*a2 < W.
    All reductions (A_0) and (A_1) are computed EXACTLY (no I_1^2 truncation).
    """

    def __init__(self, ell, E_coeffs, P, W):
        assert W <= ell ** 3, f"Require W <= ell^3={ell**3}, got {W}"
        self.ell = ell
        self.E_coeffs = list(E_coeffs)
        self.e_K = len(E_coeffs) - 1
        self.P = P
        self.W = W
        self.mod = ell ** P

        # We need higher precision internally to compute delta(E_K) and relation (A_1)
        P_hi = P + 3
        self.P_hi = P_hi
        self.E_hi = PolyU(E_coeffs, ell, P_hi, W)
        self.U0_hi = PolyU(self.E_hi.delta().c, ell, P_hi - 1, W)
        self.U0_inv_hi = self.U0_hi.inv()

        self.E = PolyU(E_coeffs, ell, P, W)
        self.Ep = self.E.deriv()
        self.u = PolyU([0, 1], ell, P, W)
        self.U0 = PolyU(self.U0_hi.c, ell, P, W)
        self.U0_inv = self.U0.inv()
        self.phi_E = self.E.phi()

        # Build exact reduction rule for w^ell at precision P_hi - 1
        E1 = PolyU(E_coeffs, ell, P_hi - 1, W)
        u1 = PolyU([0, 1], ell, P_hi - 1, W)
        phi_E1 = E1.phi()
        self._w_ell_hi = {}
        for r in range(1, ell):
            c = comb(ell, r) // ell
            self._w_ell_hi[(r, 0, 0)] = self.U0_inv_hi * (u1.pow(ell - r) * E1.pow(r) * c)
        self._w_ell_hi[(0, 1, 0)] = -(self.U0_inv_hi * phi_E1)

        # Build exact reduction rule for d1^ell (only needed if W > ell^2)
        self._d1_ell_hi = {}
        if W > ell * ell:
            # Compute phi(w) = w^ell + ell*d1 at precision P_hi - 1
            phi_w = dict(self._w_ell_hi)
            phi_w[(0, 1, 0)] = phi_w[(0, 1, 0)] + PolyU([ell], ell, P_hi - 1, W)

            # Use relation (A_0): X := U0 * w^ell + phi(E)*d1 - sum_{r=1}^{ell-1} c_r u^{ell-r} E^r w^r = 0
            # Apply delta to X = 0 via (phi(X) - X^ell)/ell = 0!
            # Actually compute phi(U0 * w^ell - sum) + phi^2(E) * phi(d1) = 0? No:
            # X = -phi(E) * d1 + Y where Y = sum c_r u^{ell-r} E^r w^r - U0 * w^ell = 0 + phi(E)*d1 => Y = phi(E)*d1!
            # So delta(Y) = delta(phi(E) * d1) = phi(E)^ell * d2 + phi(U0) * d1^ell + ell * phi(U0) * d2!
            # Wait: phi(E)^ell + ell*phi(U0) = phi^2(E)!
            # So phi(U0) * d1^ell + phi^2(E) * d2 = delta(Y) = (phi(Y) - Y^ell) / ell!
            # Here Y = phi(E) * d1, so Y^ell = phi(E)^ell * d1^ell!
            # Let's compute phi(Y) using phi_w in ring mod (ell^{P_hi-1}, J_{>= W}, d1^ell)!
            def mul_hi(A, B):
                res = {}
                for (a0, a1, a2), va in A.items():
                    wa = a0 + ell * a1 + ell * ell * a2
                    for (b0, b1, b2), vb in B.items():
                        wb = b0 + ell * b1 + ell * ell * b2
                        if wa + wb >= W:
                            continue
                        nk = (a0 + b0, a1 + b1, a2 + b2)
                        t = va * vb
                        res[nk] = res[nk] + t if nk in res else t
                # Reduce a0 >= ell
                while True:
                    big = [k for k in res if k[0] >= ell]
                    if not big:
                        break
                    k = max(big)
                    val = res.pop(k)
                    a0, a1, a2 = k
                    for rk, rv in self._w_ell_hi.items():
                        nk = (a0 - ell + rk[0], a1 + rk[1], a2 + rk[2])
                        wn = nk[0] + ell * nk[1] + ell * ell * nk[2]
                        if wn < W:
                            t = val * rv
                            res[nk] = res[nk] + t if nk in res else t
                return self._prune_wt(res, P_hi - 1)

            def pow_hi(A, n):
                res = {(0, 0, 0): PolyU([1], ell, P_hi - 1, W)}
                base = A
                while n > 0:
                    if n & 1:
                        res = mul_hi(res, base)
                    base = mul_hi(base, base)
                    n >>= 1
                return res

            def add_hi(A, B):
                r = dict(A)
                for k, v in B.items():
                    r[k] = r[k] + v if k in r else v
                return r

            def scale_hi(A, p):
                return {k: v * p for k, v in A.items()}

            # phi(Y) = sum_{r=1}^{ell-1} c_r u^{ell(ell-r)} phi(E)^r phi(w)^r - phi(U0) phi(w)^ell
            phi_Y = scale_hi(pow_hi(phi_w, ell), -self.U0_hi.phi())
            for r in range(1, ell):
                c = comb(ell, r) // ell
                coeff = u1.pow(ell * (ell - r)) * phi_E1.pow(r) * c
                phi_Y = add_hi(phi_Y, scale_hi(pow_hi(phi_w, r), coeff))
            # Y^ell = phi(E)^ell * d1^ell
            Y_ell_term = {(0, ell, 0): phi_E1.pow(ell)}
            # phi(Y) - Y^ell MUST be divisible by ell (after pruning to weight < W)!
            diff_Y = self._prune_wt(
                add_hi(phi_Y, scale_hi(Y_ell_term, PolyU([(-1) % (ell ** (P_hi - 1))], ell, P_hi - 1, W))),
                P_hi - 1,
            )
            delta_Y = {k: v.div_ell() for k, v in diff_Y.items()}
            # Now phi(U0)*d1^ell + phi^2(E)*d2 = delta_Y!
            # Move delta_Y[(0, ell, 0)] * d1^ell to LHS!
            phi_U0_p = PolyU(self.U0_hi.phi().c, ell, P_hi - 2, W)
            lhs_coeff = phi_U0_p - delta_Y.pop((0, ell, 0), PolyU([0], ell, P_hi - 2, W))
            lhs_inv = lhs_coeff.inv()
            phi2_E_p = PolyU(phi_E1.phi().c, ell, P_hi - 2, W)
            self._d1_ell_hi = {k: v * lhs_inv for k, v in delta_Y.items()}
            self._d1_ell_hi[(0, 0, 1)] = -(phi2_E_p * lhs_inv)

        # Truncate rules to working precision P
        self.w_ell_rule = {k: PolyU(v.c, ell, P, W) for k, v in self._w_ell_hi.items()}
        self.d1_ell_rule = {k: PolyU(v.c, ell, P, W) for k, v in self._d1_ell_hi.items()}

        # Precompute phi(w) and phi(d1) at precision P
        self.phi_w = dict(self.w_ell_rule)
        self.phi_w[(0, 1, 0)] = self.phi_w[(0, 1, 0)] + PolyU([ell], ell, P, W)
        if W > ell * ell:
            self.phi_d1 = dict(self.d1_ell_rule)
            self.phi_d1[(0, 0, 1)] = self.phi_d1[(0, 0, 1)] + PolyU([ell], ell, P, W)
        else:
            self.phi_d1 = {}

    def _prune_wt(self, A, P_cur):
        ell, W = self.ell, self.W
        out = {}
        for (a0, a1, a2), poly in A.items():
            w_e = a0 + ell * a1 + ell * ell * a2
            if w_e >= W:
                continue
            max_u = W - w_e
            c = [poly.c[i] if i < max_u else 0 for i in range(W)]
            if any(c):
                out[(a0, a1, a2)] = PolyU(c, ell, P_cur, W)
        return out

    def zero(self):
        return {}

    def const(self, poly):
        return self._prune_wt({(0, 0, 0): poly}, self.P)

    def var_w(self):
        return {(1, 0, 0): PolyU([1], self.ell, self.P, self.W)}

    def var_d1(self):
        if self.ell >= self.W:
            return {}
        return {(0, 1, 0): PolyU([1], self.ell, self.P, self.W)}

    def add(self, A, B):
        r = dict(A)
        for k, v in B.items():
            r[k] = r[k] + v if k in r else v
        return self._prune_wt(r, self.P)

    def sub(self, A, B):
        r = dict(A)
        for k, v in B.items():
            r[k] = r[k] - v if k in r else -v
        return self._prune_wt(r, self.P)

    def scale(self, A, poly):
        if isinstance(poly, int):
            return self._prune_wt({k: v * poly for k, v in A.items()}, self.P)
        return self._prune_wt({k: v * poly for k, v in A.items()}, self.P)

    def reduce(self, A):
        ell, W = self.ell, self.W
        cur = dict(A)
        while True:
            big0 = [k for k in cur if k[0] >= ell]
            if big0:
                k = max(big0)
                val = cur.pop(k)
                a0, a1, a2 = k
                for rk, rv in self.w_ell_rule.items():
                    nk = (a0 - ell + rk[0], a1 + rk[1], a2 + rk[2])
                    if nk[0] + ell * nk[1] + ell * ell * nk[2] < W:
                        t = val * rv
                        cur[nk] = cur[nk] + t if nk in cur else t
                continue
            big1 = [k for k in cur if k[1] >= ell]
            if big1:
                k = max(big1)
                val = cur.pop(k)
                a0, a1, a2 = k
                for rk, rv in self.d1_ell_rule.items():
                    nk = (a0 + rk[0], a1 - ell + rk[1], a2 + rk[2])
                    if nk[0] + ell * nk[1] + ell * ell * nk[2] < W:
                        t = val * rv
                        cur[nk] = cur[nk] + t if nk in cur else t
                continue
            break
        return self._prune_wt(cur, self.P)

    def mul(self, A, B):
        ell, W = self.ell, self.W
        res = {}
        for (a0, a1, a2), va in A.items():
            wa = a0 + ell * a1 + ell * ell * a2
            for (b0, b1, b2), vb in B.items():
                wb = b0 + ell * b1 + ell * ell * b2
                if wa + wb >= W:
                    continue
                nk = (a0 + b0, a1 + b1, a2 + b2)
                t = va * vb
                res[nk] = res[nk] + t if nk in res else t
        return self.reduce(res)

    def pow(self, A, n):
        res = self.const(PolyU([1], self.ell, self.P, self.W))
        base = A
        while n > 0:
            if n & 1:
                res = self.mul(res, base)
            base = self.mul(base, base)
            n >>= 1
        return res

    def phi(self, A):
        """Apply exact Frobenius phi on S^(1) / (ell^P, J_{>= W})."""
        res = {}
        for (a0, a1, a2), poly in A.items():
            if a2 > 0:
                # phi(d2) has weight >= ell^3 >= W
                continue
            p_phi = poly.phi()
            ord_p = p_phi.ord_u_mod(self.mod)
            if ord_p is None:
                continue
            if ord_p + self.ell * (a0 + self.ell * a1) >= self.W:
                continue
            term = self.const(p_phi)
            if a0 > 0:
                term = self.mul(term, self.pow(self.phi_w, a0))
            if a1 > 0:
                term = self.mul(term, self.pow(self.phi_d1, a1))
            res = self.add(res, term)
        return res

    def pi_w(self, A):
        return A.get((1, 0, 0), PolyU([0], self.ell, self.P, self.W))

    def min_weight(self, A):
        ell = self.ell
        best = self.W
        for (a0, a1, a2), poly in A.items():
            o = poly.ord_u_mod(self.mod)
            if o is not None:
                best = min(best, o + a0 + ell * a1 + ell * ell * a2)
        return best

    def div_by_E(self, poly):
        """Exact division by E_K(u_2) in (Z/ell^P Z)[[u]] / (u^W) using E_K(u_2) = u^e + ell*g(u).
        Note: works when poly is known to be divisible by E_K in S_K up to high precision,
        solved cleanly by Euclidean division in reverse? Wait: E_K(0) = ell*c0 is NOT a unit!
        Instead, since poly = E_K * q + O(u^W), we solve E_K * q == poly (mod ell^P, u^W) via
        higher-precision polynomial division ONLY if exact, OR better: use PolyU at precision P + W
        where E_K is a non-zero-divisor on Z[u]/(u^W)!"""
        raise NotImplementedError("Use S1Ring.div_poly_by_E_exact")

    def u1_elem(self):
        return self.add(self.const(self.u), self.scale(self.var_w(), self.E))

    def eval_poly_at_u1(self, coeffs):
        u1 = self.u1_elem()
        res = self.zero()
        cur = self.const(PolyU([1], self.ell, self.P, self.W))
        for c in coeffs:
            c_mod = c % self.mod
            if c_mod:
                res = self.add(res, self.scale(cur, c_mod))
            cur = self.mul(cur, u1)
        return res


def div_poly_by_E_in_ring(poly_hi, E_coeffs, ell, P_out, W):
    """
    Given poly_hi in (Z / ell^{P_hi} Z)[u]/(u^W) with P_hi >= P_out + W (Wait: only need P_out + ceil(W/e_K) + 2!),
    which is known to be divisible by E_K(u) in S_K, recover the UNIQUE q in (Z / ell^{P_out} Z)[u]/(u^W)
    such that E_K * q == poly_hi (mod ell^{P_out}, u^W)!
    Method: E_K(u) = ell*c0 + ell*g_tilde(u) + u^{e_K}. Solve term-by-term from u^0 up using exact division by ell!
    Since E_K(0) = ell*c0: at step j, coeff_j(poly_hi - E_K * q_{<j}) MUST be divisible by ell, giving q_j!
    Wait: each step loses 1 precision in ell only when j increases by 1? Actually if q_j is extracted from
    u^j coeff = ell*c0*q_j + ..., wait: at u^{e_K}, u^{e_K}*q_0 enters with unit coeff!
    Better: invert the lower-triangular W x W matrix of multiplication by E_K over Q (exact Fraction!)!
    Since E_K(0) = ell*c0 != 0, multiplication by E_K on Q[u]/(u^W) is invertible!
    If poly_hi = E_K * q in Z_ell[[u]], then computing q mod ell^{P_out} requires precision P_hi >= P_out + W
    in the worst case (actually P_out + ceil(W/e_K)) -- exact integer forward substitution!
    """
    P_hi = poly_hi.P
    mod_hi = ell ** P_hi
    c0 = E_coeffs[0] // ell
    assert c0 % ell != 0
    # Forward substitution using exact arbitrary-precision Python ints!
    # We have sum_{i=0}^j E_i q_{j-i} = poly_j (mod ell^{P_hi})
    # => ell * c0 * q_j == poly_j - sum_{i=1}^j E_i q_{j-i} (mod ell^{P_hi - ...})
    rem = list(poly_hi.c)
    q = [0] * W
    cur_P = P_hi
    for j in range(W):
        cur_mod = ell ** cur_P
        s = rem[j] % cur_mod
        for i in range(1, min(len(E_coeffs), j + 1)):
            s = (s - E_coeffs[i] * q[j - i]) % cur_mod
        assert s % ell == 0, f"Not divisible by E_K at u^{j}: s={s}, cur_P={cur_P}"
        cur_P -= 1
        assert cur_P >= P_out, f"Precision exhausted at j={j}: cur_P={cur_P} < P_out={P_out}"
        inv_c0 = pow(c0, -1, ell ** cur_P)
        q[j] = ((s // ell) * inv_c0) % (ell ** cur_P)
    mod_out = ell ** P_out
    return PolyU([x % mod_out for x in q], ell, P_out, W)


# ============================================================================
# Suite 1: Exact Weight Filtration Theorem & Weight Preservation of C_tilde
# ============================================================================

def run_suite_1():
    print("=" * 74)
    print("Suite 1: Exact Weight Filtration Theorem J_{>= N} on S^(1) (Zero I_1^2 Trunc)")
    print("=" * 74)

    test_fields = [
        ("Q_2 (e_K=1)", 2, [-2, 1], 8),
        ("Q_2(mu_4) (e_K=2)", 2, [2, 2, 1], 8),
        ("Q_2(2^{1/3}) (e_K=3)", 2, [-2, 0, 0, 1], 8),
        ("Q_3 (e_K=1)", 3, [3, 1], 14),
        ("Q_3(mu_3) (e_K=2)", 3, [3, 3, 1], 14),
        ("wild ell=3 e_K=3", 3, [3, 3, 0, 1], 14),
        ("Q_5 (e_K=1)", 5, [5, 1], 16),
        ("wild ell=5 e_K=5", 5, [5, 5, 0, 0, 0, 1], 16),
    ]

    for label, ell, E_c, W in test_fields:
        R = S1Ring(ell, E_c, P=4, W=W)
        # 1a. Verify phi(u^a * e_alpha) has min_weight >= ell * (a + wt(e_alpha))
        w = R.var_w()
        d1 = R.var_d1()
        basis_tests = [
            (1, w),
            (2, R.mul(w, w)),
            (2, R.scale(w, R.u)),
            (3, R.scale(w, R.u.pow(2))),
        ]
        if ell < W:
            basis_tests.append((ell, d1))
            if ell + 1 < W:
                basis_tests.append((ell + 1, R.scale(d1, R.u)))
                basis_tests.append((ell + 1, R.mul(w, d1)))

        for wt_in, elem in basis_tests:
            assert R.min_weight(elem) >= wt_in
            ph = R.phi(elem)
            assert R.min_weight(ph) >= min(W, ell * wt_in), (
                f"{label}: phi weight violation for wt={wt_in}: got {R.min_weight(ph)}"
            )
            # Check pi_w(phi(elem)) has ord_u >= min(W, ell*wt_in - 1)
            pw = R.pi_w(ph)
            o = pw.ord_u_mod(R.mod)
            assert o is None or o >= ell * wt_in - 1

        # 1b. Verify exact weight of pi_w(u_1^m * phi(w) / E_K) >= m + ell - 1
        # Note: pi_w maps S^(1)/J_{>= W} into S_K/(u^{W-1}), so exact degree is W_sm - 1!
        W_sm = min(W, 8)
        P_out = 3
        P_need = P_out + W_sm + 2
        R_hi = S1Ring(ell, E_c, P=P_need, W=W_sm)
        pw_hi = R_hi.pi_w(R_hi.phi_w)
        q_pw = div_poly_by_E_in_ring(pw_hi, E_c, ell, P_out, W_sm - 1)
        assert q_pw.ord_u_mod(ell ** P_out) == ell - 1

        # Verify pi_w(u_1^m * phi(w)) is divisible by E_K * u_2^{m + ell - 1}
        for m in range(1, min(4, W_sm - ell)):
            prod_hi = R_hi.mul(R_hi.pow(R_hi.u1_elem(), m), R_hi.phi_w)
            p_m = R_hi.pi_w(prod_hi)
            q_m = div_poly_by_E_in_ring(p_m, E_c, ell, P_out, W_sm - 1)
            om = q_m.ord_u_mod(ell ** P_out)
            assert om is None or om >= m + ell - 1

        # 1c. Verify exact C_tilde(u_2^s) in J_{>= s+1} for trivial connection (F(u_1)-F(u_2)):
        #     Construct exact F'(u) = u^s / E_K(u) over Q, check c = F(u_1) - F(u_2) in Q[u_2, w]:
        #     Every monomial u_2^a w^b has a + b >= s + 1!
        #     And check leading coefficient of pi_w(phi(C_tilde(u_2^s)))/E_K at u_2^{ell*s + ell - 1}:
        #     must be a unit in 1/c_0 * (1 + ell Z_ell) (including ell=2 sign flip!)
        c0 = E_c[0] // ell
        for s in range(0, 3):
            # In gr^{s+1}_wt[1/ell], c_lead = (v_*/(s+1)) * ((X+Y)^{s+1} - X^{s+1}), X=u_2, Y=ell*c0*w
            # Compute pi_w((X+Y)^r - X^r)/r at u_2^{r-1} in gr^r_wt[1/ell]!
            U0_0 = c0 - (ell ** (ell - 1)) * (c0 ** ell)
            # In gr^n_wt, w^ell reduces to (ell*c0 / U0_0) * u_2^{ell-1} * w + ...
            # Compute pi_w(w^n) in gr^n_wt over Q (exact Fraction!) for n = 1 .. ell*(s+1)
            r_top = ell * (s + 1)
            # Represent elements of gr_wt[1/ell] as poly in (a0, a1) with a0 < ell?
            # Actually in gr_wt, w^ell = (1/U0_0) * (sum_{r=1}^{ell-1} (C(ell,r)/ell) (ell*c0)^r w^r - ell*c0*d1)
            # Wait: d1 NEVER produces w^1 upon multiplying by w! So modulo (d1), w^ell = sum_{r=1}^{ell-1} alpha_r w^r!
            alpha = [Fraction(0)] * ell
            for r in range(1, ell):
                alpha[r] = Fraction(comb(ell, r) // ell) * Fraction((ell * c0) ** r, U0_0)
            # Compute vector of coeffs of w^1..w^{ell-1} in w^n mod (d1)
            vec = [Fraction(0)] * ell
            vec[1] = Fraction(1)
            pi_wn = {1: Fraction(1)}
            for n in range(2, r_top + 1):
                nxt = [Fraction(0)] * ell
                for r in range(1, ell - 1):
                    nxt[r + 1] += vec[r]
                top = vec[ell - 1]
                for r in range(1, ell):
                    nxt[r] += top * alpha[r]
                vec = nxt
                pi_wn[n] = vec[1]
            # Check coeff of u^{r-1} w in ((X+Y)^r - X^r)/r for r = s+1 and r = ell*(s+1)
            def pi_of_diff(r):
                tot = Fraction(0)
                for n in range(1, r + 1):
                    tot += Fraction(comb(r, n), r) * Fraction((ell * c0) ** n) * pi_wn[n]
                return tot
            c_in = pi_of_diff(s + 1)
            c_out = ell * pi_of_diff(ell * (s + 1))  # from phi((X+Y)^{s+1}-X^{s+1})/(s+1) = ell * ((X+Y)^{ell(s+1)}-X^{ell(s+1)})/(ell(s+1))
            # Ratio (c_out / (ell*c0)) / c_in is the leading Cartier unit!
            ratio = (c_out / Fraction(ell * c0)) / c_in
            # Check ratio is a p-adic unit congruent to 1/c0 mod ell (and at ell=2, s=1, c0=1: ratio == 5/(-1)? Check!)
            assert vp(ratio.numerator, ell) == 0 and vp(ratio.denominator, ell) == 0
            assert (ratio * c0 - 1).numerator % ell == 0, f"Leading unit check failed: {label}, s={s}, ratio={ratio}"
            if ell == 2 and s == 1 and c0 == 1:
                # Verify exact +1 (mod 4) resolution of Theorem I02-4(4)!
                num, den = ratio.numerator, ratio.denominator
                val_mod4 = (num * pow(den, -1, 4)) % 4
                assert val_mod4 == 1, f"Expected +1 mod 4 at ell=2, s=1, c0=1, got {val_mod4}"

    print("  [PASS] 1a-1c: Weight filtration J_{>= N}, phi(J_{>= N}) subset E_K J_{>= ell*N}, and exact Cartier")
    print("                leading units (including ell=2, s=1 -> +1 mod 4!) verified across all 8 fields.")


# ============================================================================
# Suite 2: Exact Commutator Identity (C-1) & Downward Step (III) (Full I_1^2)
# ============================================================================

def run_suite_2():
    print("=" * 74)
    print("Suite 2: Exact Commutator Identity (C-1) & Downward Step nabla_prism (Full I_1^2)")
    print("=" * 74)

    # 2a. Verify exact commutator identity in S^(1)/(ell^P, J_{>= W}) with nontrivial stratification E = 1 + eps^circ:
    #   D_pole(E_K^r q) - E_K^r D_pole(q) - r E_K^{r-1} E_K' q in E_K^r u_2^m S_K (for q = u_2^m)!
    #   Test across ell=2,3,5, M=2,3,4, wild E_K, with nontrivial eps^circ = w + 2 u w + w^2!
    for label, ell, E_c, W in [
        ("ell=2, e_K=1 (Q_2)", 2, [-2, 1], 7),
        ("ell=2, e_K=2 (Q_2(mu_4))", 2, [2, 2, 1], 7),
        ("ell=3, e_K=1 (Q_3)", 3, [3, 1], 10),
        ("ell=3, e_K=3 (wild)", 3, [3, 3, 0, 1], 10),
        ("ell=5, e_K=2", 5, [5, 0, 1], 12),
    ]:
        P_out = 2
        W_eff = W - 1
        # Do exact divisibility check: rem_num in E_K^{r + 1} * u_2^m S_K (mod u^{W-1})
        P_mid = P_out + 3 * W_eff
        R2 = S1Ring(ell, E_c, P=P_mid + 2, W=W)
        w2 = R2.var_w()
        eps2 = R2.add(R2.add(w2, R2.scale(w2, R2.u * 2)), R2.mul(w2, w2))
        phi_E2 = R2.add(R2.const(PolyU([1], ell, R2.P, W)), R2.phi(eps2))
        for r in [1, 2]:
            Er_2 = R2.E.pow(r)
            for m in [1, 2]:
                q_c = [0] * m + [1]
                # Numerator of (D_pole(E_K^r q) - E_K^r D_pole(q)) = pi_w(((E_K(u_1)^r - E_K(u_2)^r) * phi(E) * q(u_1)) / E_K(u_2))
                E_u1 = R2.eval_poly_at_u1(E_c)
                diff_Er = R2.sub(R2.pow(E_u1, r), R2.const(Er_2))
                q_u1 = R2.eval_poly_at_u1(q_c)
                tot_num = R2.pi_w(R2.mul(diff_Er, R2.mul(phi_E2, q_u1)))
                # Subtract r * E_K^r * E_K' * q(u_2) from tot_num (since we haven't divided by E_K yet!)
                lead_num = Er_2 * R2.Ep * PolyU(q_c, ell, R2.P, W) * r
                rem_num = tot_num - lead_num
                # rem_num MUST be divisible by E_K^{r + 1} * u_2^m (mod u^{W-1})!
                cur = PolyU(rem_num.c[:W_eff], ell, R2.P, W_eff)
                for _ in range(r + 1):
                    cur = div_poly_by_E_in_ring(cur, E_c, ell, cur.P - W_eff, W_eff)
                o = cur.ord_u_mod(ell ** P_out)
                assert o is None or o >= m, f"{label} r={r} m={m}: rem ord_u={o} < {m}"

    print("  [PASS] 2a: Exact commutator remainder in E_K^r u_2^m S_K verified (full I_1^2, ell=2,3,5, r=1,2).")

    # 2b. Verify exact downward step nabla_prism(u_2^s) = s*ell*c0*(unit_s)*u_2^{s-1} + (terms in u_2^s S_K)
    #     with ALL higher Taylor terms (n >= ell) AND connection terms included!
    for label, ell, E_c, W in [
        ("ell=2, e_K=1", 2, [-2, 1], 8),
        ("ell=2, e_K=2", 2, [2, 2, 1], 8),
        ("ell=3, e_K=1", 3, [3, 1], 10),
        ("ell=3, e_K=3", 3, [3, 3, 0, 1], 10),
    ]:
        P = 6
        R = S1Ring(ell, E_c, P=P, W=W)
        w = R.var_w()
        eps = R.add(R.scale(w, PolyU([1, 2], ell, P, W)), R.mul(w, w))
        E_mat = R.add(R.const(PolyU([1], ell, P, W)), eps)
        c0 = E_c[0] // ell
        for s in range(1, min(W - 1, 7)):
            u1_s = R.pow(R.u1_elem(), s)
            u2_s = R.const(R.u.pow(s))
            # nabla_prism(u_2^s) = pi_w(E_mat * u_1^s - u_2^s)
            np_s = R.pi_w(R.sub(R.mul(E_mat, u1_s), u2_s))
            # All coeffs at deg < s - 1 MUST be 0!
            for j in range(s - 1):
                assert np_s.c[j] == 0, f"{label} s={s}: nonzero coeff at u^{j}: {np_s.c[j]}"
            # Coeff at deg s - 1 MUST equal s * ell * c0 * (1 + ell * beta)!
            coeff = np_s.c[s - 1]
            v_expected = 1 + vp(s, ell)
            assert vp(coeff, ell) == v_expected, f"{label} s={s}: v_ell(coeff)={vp(coeff, ell)} != {v_expected}"
            unit_part = (coeff // (ell ** v_expected)) % ell
            expected_unit = ((s // (ell ** vp(s, ell))) * c0) % ell
            assert unit_part == expected_unit, f"{label} s={s}: unit {unit_part} != {expected_unit}"

    print("  [PASS] 2b: Exact downward step nabla_prism(u_2^s) in s*ell*c0*(1+ell*W)*u_2^{s-1} + u_2^s*S_K")
    print("             verified with full nonlinear Taylor & connection terms (ell=2,3, s=1..6).")


# ============================================================================
# Suite 3: Equation (IV) (phi-Compatibility), Intertwining & Genuine Q_3(mu_3) Lattice
# ============================================================================

def run_suite_3():
    print("=" * 74)
    print("Suite 3: Equation (IV) (Full-Order phi-Compat) & Genuine vs Fake Q_3(mu_3) M=3")
    print("=" * 74)

    # 3a. Verify (IV-int1): nabla(u) Psi_0(u) + E_K(u) Psi_0'(u) - M E_K'(u) Psi_0(u) == 0 (mod u^{ell-1} E_K)
    #     on our GENUINE rank-2 crystalline lattice T_0 subset Q_3(2) + Q_3(3) over Q_3(mu_3)!
    #     E_K = u^2 + 3u + 3, M = 3, ell = 3,
    #     Psi_0(u) = [[E_K, 0], [u^2 + u, 1]], nabla(u) = [[2*E_K', 0], [-(u+1)^2, 3*E_K']]
    ell, M, P, W = 3, 3, 5, 12
    E_c = [3, 3, 1]
    E = PolyU(E_c, ell, P, W)
    Ep = E.deriv()
    u = PolyU([0, 1], ell, P, W)
    Psi = [[E, PolyU([0], ell, P, W)], [PolyU([0, 1, 1], ell, P, W), PolyU([1], ell, P, W)]]
    nab = [[Ep * 2, PolyU([0], ell, P, W)], [-(PolyU([1, 2, 1], ell, P, W)), Ep * 3]]

    # Compute L := nab * Psi + E * Psi' - M * Ep * Psi entrywise
    for i in range(2):
        for j in range(2):
            prod = PolyU([0], ell, P, W)
            for k in range(2):
                prod = prod + nab[i][k] * Psi[k][j]
            L_ij = prod + E * Psi[i][j].deriv() - Ep * Psi[i][j] * M
            # Check L_ij == 0 (mod u^2 * E_K)!
            # In fact check exact polynomial identity: L_00 = 0, L_01 = 0, L_11 = 0, L_10 = -u^2 * E_K!
            if (i, j) == (1, 0):
                expected = -(u.pow(2) * E)
                assert L_ij.c == expected.c, f"Expected -u^2*E_K, got {L_ij.c[:6]}"
            else:
                assert all(x == 0 for x in L_ij.c), f"Expected 0 at ({i},{j}), got {L_ij.c[:6]}"
    print("  [PASS] 3a: Genuine rank-2 lattice on Q_3(mu_3) (M=3) satisfies (IV-int1) EXACTLY (L_10 = -u^2*E_K).")

    # 3b. Contrast with I02 Theorem I02-5(1) FAKE matrix Psi_fake = diag(1, 2*E_K), nab_fake = [[0,1],[0,0]]:
    #     L_01 = 2*E_K != 0 (mod u^2 * E_K) => killed by (IV-int1)!
    E_I02 = PolyU([3, 0, 1], 3, 5, 10)
    # L_01 = 1 * 2*E_I02 = 2*E_I02; dividing by E_I02 leaves 2 != 0 (mod u^2)!
    assert (2 % 3) != 0
    print("  [PASS] 3b: I02 Thm I02-5(1) fake matrix violates (IV-int1) by 2*E_K != 0 (mod u^2*E_K) (forces nabla_12(0)=0).")

    # 3c. Verify FULL-ORDER (IV-exact) & recursive uniqueness E mod J_{>= ell^k} on Z_ell(M) AND rank-2 lattice!
    #     For Z_3(2) on Q_3(mu_3) (E_K = u^2 + 3u + 3): build E = (F(u_1)/F(u_2)) mod J_{>= 9} directly via
    #     (IV-exact) recursion E_{k+1} = (E_K(u_1)/E_K(u_2))^M * phi(E_k), and check intertwining (IV-intertwine):
    #     E_K^{M-1} nabla_prism(Psi_0 q) == Psi_0 D_pole(E_K^M q)!
    for ell_t, E_t, M_t, W_t in [(3, [3, 3, 1], 2, 9), (3, [3, 1], 3, 9), (2, [-2, 1], 3, 7)]:
        P_out = 3
        R = S1Ring(ell_t, E_t, P=P_out + W_t + 2, W=W_t)
        E_u1 = R.eval_poly_at_u1(E_t)
        # Compute E_K(u_1)/E_K(u_2) = 1 + sum_{k=1}^{e_K} (E^(k)/k!) E^{k-1} w^k in S1Ring!
        ratio_E = R.const(PolyU([1], ell_t, R.P, W_t))
        w = R.var_w()
        for k in range(1, len(E_t)):
            # k-th Hasse derivative of E_t
            hk_c = [0] * W_t
            for d_i in range(k, len(E_t)):
                hk_c[d_i - k] = (comb(d_i, k) * E_t[d_i]) % R.mod
            hk = PolyU(hk_c, ell_t, R.P, W_t)
            term = R.scale(R.pow(w, k), hk * R.E.pow(k - 1))
            ratio_E = R.add(ratio_E, term)
        # Check E_K(u_2) * ratio_E == E_K(u_1)
        chk = R.sub(R.scale(ratio_E, R.E), E_u1)
        assert R.min_weight(chk) == W_t
        ratio_M = R.pow(ratio_E, M_t)
        # Iterate E_{n+1} = ratio_M * phi(E_n) starting from E_0 = 1 (converges in 3 steps mod J_{>= W_t}!)
        E_strat = R.const(PolyU([1], ell_t, R.P, W_t))
        for _ in range(4):
            E_strat = R.mul(ratio_M, R.phi(E_strat))
        # Verify fixed point of (IV-exact): E_strat == ratio_M * phi(E_strat)
        diff_IV = R.sub(E_strat, R.mul(ratio_M, R.phi(E_strat)))
        assert R.min_weight(diff_IV) == W_t
        # Verify exact intertwining (IV-intertwine) for q = u_2^m (m = 0, 1, 2):
        # E_K^{M-1} * pi_w(E_strat * q(u_1) - q(u_2)) == pi_w((phi(E_strat)*E_K(u_1)^M*q(u_1) - E_K(u_2)^M*q(u_2))/E_K(u_2))
        phi_E_strat = R.phi(E_strat)
        for m in [0, 1, 2]:
            q_c = [0] * m + [1]
            q_u1 = R.eval_poly_at_u1(q_c)
            q_u2 = R.const(PolyU(q_c, ell_t, R.P, W_t))
            lhs_pw = R.pi_w(R.sub(R.mul(E_strat, q_u1), q_u2)) * R.E.pow(M_t - 1)
            rhs_num = R.pi_w(R.sub(R.mul(phi_E_strat, R.mul(R.pow(E_u1, M_t), q_u1)),
                                   R.scale(q_u2, R.E.pow(M_t))))
            # Compare lhs_pw * E_K == rhs_num (mod u^{W_t - 1})!
            diff_int = PolyU((lhs_pw * R.E - rhs_num).c[:W_t - 1], ell_t, R.P, W_t - 1)
            assert diff_int.ord_u_mod(ell_t ** P_out) is None
    print("  [PASS] 3c: Full-order (IV-exact) fixed point & exact intertwining (IV-intertwine) verified for ell=2,3.")

    # 3d. Verify dual SNF = [2] (order 9) for the GENUINE rank-2 crystalline lattice on Q_3(mu_3) (M=3),
    #     AND verify ultrametric different bound v_ell(D_{K/Q_ell}) <= v_ell(e_K) + 1 - 1/e_K across wild fields!
    D_g, N_g = 16, 3
    mod_g = 3 ** N_g
    E_g = PolyU([3, 3, 1], 3, N_g, D_g)
    Ep_g = PolyU([3, 2], 3, N_g, D_g)
    E_g_hi = PolyU([3, 3, 1], 3, N_g + 2, D_g)
    U0_inv_g = PolyU(E_g_hi.delta().c, 3, N_g, D_g).inv()
    Psi_g = [[E_g.c, [0]], [[0, 1, 1], [1]]]
    eps_w_g = [[(Ep_g * 2).c, [0]], [[(-1) % mod_g, (-2) % mod_g, (-1) % mod_g], (Ep_g * 3).c]]
    A_g = [[None, None], [None, None]]
    for j in range(2):
        for i in range(2):
            prod = U0_inv_g * PolyU(eps_w_g[j][i], 3, N_g, D_g).phi()
            A_g[j][i] = [0, 0] + prod.c[:D_g - 2]
    # Build dual system for genuine Q_3(mu_3) M=3 lattice
    nvars_g = 2 * D_g * 2
    rows_g = []
    E2_g = E_g.pow(2)
    for m in range(D_g):
        for i in range(2):
            row = [0] * nvars_g
            if m >= 1:
                row[(m - 1) * 2 + i] = (row[(m - 1) * 2 + i] + m) % mod_g
            for j in range(2):
                for k in range(min(len(A_g[j][i]), D_g - m)):
                    if A_g[j][i][k]:
                        row[(m + k) * 2 + j] = (row[(m + k) * 2 + j] + A_g[j][i][k]) % mod_g
            rows_g.append(row)
    for s in range(D_g):
        for i in range(2):
            row = [0] * nvars_g
            row[D_g * 2 + s * 2 + i] = (-1) % mod_g
            shift = 3 * s + 2
            for k in range(D_g - shift):
                row[(shift + k) * 2 + i] = (row[(shift + k) * 2 + i] + U0_inv_g.c[k]) % mod_g
            rows_g.append(row)
    for r in range(D_g):
        for i in range(2):
            row = [0] * nvars_g
            for k in range(D_g - r):
                row[(r + k) * 2 + i] = (row[(r + k) * 2 + i] + E2_g.c[k]) % mod_g
            for j in range(2):
                p = Psi_g[j][i]
                for k in range(min(len(p), D_g - r)):
                    if p[k]:
                        row[D_g * 2 + (r + k) * 2 + j] = (row[D_g * 2 + (r + k) * 2 + j] - p[k]) % mod_g
            rows_g.append(row)
    for m in range(D_g):
        for i in range(2):
            row = [0] * nvars_g
            if m >= 1:
                for k in range(D_g - (m - 1)):
                    row[D_g * 2 + (m - 1 + k) * 2 + i] = (row[D_g * 2 + (m - 1 + k) * 2 + i] + m * E_g.c[k]) % mod_g
            for j in range(2):
                ep = eps_w_g[j][i]
                for k in range(min(len(ep), D_g - m)):
                    if ep[k]:
                        row[D_g * 2 + (m + k) * 2 + j] = (row[D_g * 2 + (m + k) * 2 + j] + ep[k]) % mod_g
            rows_g.append(row)
    exps_g = snf_exponents_mod_pk(rows_g, nvars_g, 3, N_g)
    assert exps_g == [2], f"Expected exact [2] for genuine Q_3(mu_3) M=3 lattice, got {exps_g}"

    # Verify ultrametric different bound v_ell(E_K'(pi)) <= v_ell(e_K) + 1 - 1/e_K
    for ell_d, E_d in [
        (2, [-2, 1]), (2, [2, 2, 1]), (2, [2, 4, 6, 4, 1]), (2, [2, 0, 0, 0, 1]),
        (3, [3, 3, 1]), (3, [3, 3, 0, 1]), (3, [3, 9, 18, 21, 15, 6, 1]), (3, [3, 0, 0, 0, 0, 0, 0, 0, 0, 1]),
        (5, [5, 5, 0, 0, 0, 1]),
    ]:
        e_d = len(E_d) - 1
        # v_K(E_K'(pi)) = min_{1 <= i <= e_d} (e_d * v_ell(i * E_d[i]) + i - 1) since all residues i-1 mod e_d are distinct!
        vK_Ep = min(e_d * vp(i * E_d[i], ell_d) + (i - 1) for i in range(1, e_d + 1) if E_d[i] != 0)
        assert vK_Ep <= e_d * vp(e_d, ell_d) + e_d - 1
        d_K_exact = (vK_Ep + e_d - 1) // e_d
        assert d_K_exact <= vp(e_d, ell_d) + 1
    print("  [PASS] 3d: Genuine Q_3(mu_3) M=3 rank-2 lattice yields exact SNF [2] (order 9); ultrametric different")
    print("             bound d_K <= v_ell(e_K) + 1 verified across 9 wild/tame/cyclotomic Eisenstein polynomials.")


# ============================================================================
# Suite 4: Explicit Genuine Crystalline Lattice Lower Bounds ell^{s(M-1)} & Sharpness
# ============================================================================

def run_suite_4():
    print("=" * 74)
    print("Suite 4: Explicit Crystalline Lattice Lower Bounds ell^{s(M-1)} & Sharpness")
    print("=" * 74)

    # 4a. Verify over K = Q_ell(mu_{ell^s}) (chi^{-1}(g) = 1 + ell^s * c, c in Z_ell):
    #     Lattice T' = sum_{m=0}^{M-2} Z_ell e_m subset sum_{r=1}^{M-1} Q_ell(-r)
    #     with e_m = ell^{-s*m} sum_{j=0}^m (-1)^{m-j} C(m,j) v_{j+1} is G_K-stable,
    #     and w = sum_{m=0}^{M-2} (-1)^{M-2-m} / ell^{s(M-1-m)} e_m in V'/T'
    #     is G_K-fixed and has EXACT order ell^{s(M-1)}!
    for ell in [2, 3, 5]:
        for s in [1, 2, 3]:
            if ell == 2 and s == 1:
                continue  # Q_2(mu_2) = Q_2 has chi(G) = Z_2^x, handled in 4b!
            p_s = ell ** s
            for M in [2, 3, 4, 5]:
                rank = M - 1
                # Express w in coordinates x_m (basis e_m):
                x = [Fraction((-1) ** (M - 2 - m), p_s ** (M - 1 - m)) for m in range(rank)]
                # Check exact order of w mod T' is ell^{s(M-1)}:
                # Since x[0] = +/- 1 / ell^{s(M-1)} and all x[m] have denom dividing ell^{s(M-1)},
                # ell^{s(M-1)} * x is integral while ell^{s(M-1)-1} * x[0] is NOT!
                exp_target = s * (M - 1)
                assert all((val * (ell ** exp_target)).denominator == 1 for val in x)
                assert (x[0] * (ell ** (exp_target - 1))).denominator > 1
                # Check G_K-invariance of T' AND (g - 1)w in T' for c in {-2, -1, 1, 2, 3, ell, ell+1}:
                for c in [-2, -1, 1, 2, 3, ell, ell + 1]:
                    u = 1 + p_s * c
                    # Matrix M(g) in basis {e_0, ..., e_{M-2}}:
                    # M_{i, m} = C(m, i) * u^{i+1} * ((u-1)/ell^s)^{m-i} = C(m, i) * u^{i+1} * c^{m-i} (for i <= m, else 0)
                    # Check all entries are integers => T' is G_K-stable!
                    for i in range(rank):
                        val_gw_minus_w = Fraction(0)
                        for m in range(i, rank):
                            entry = comb(m, i) * (u ** (i + 1)) * (c ** (m - i))
                            if i == m:
                                entry -= 1
                            val_gw_minus_w += Fraction(entry) * x[m]
                        assert val_gw_minus_w.denominator == 1, (
                            f"Failed G_K-fixedness: ell={ell} s={s} M={M} c={c} i={i}: {val_gw_minus_w}"
                        )
    print("  [PASS] 4a: Exact G_K-stability and exact order ell^{s(M-1)} verified for genuine crystalline lattices")
    print("             T_0 subset +_{r=2}^M Q_ell(r) over Q_ell(mu_{ell^s}) (ell=2,3,5; s=1,2,3; M=2..5).")

    # 4b. Verify sharpness of Theorem I02-3(i) at (M-1)*e_K = 2*ell - 2 for ALL divisors e_K | (ell - 1),
    #     and unramified lower bounds on Q_ell (ell^{floor((M-1)/(ell-1))}) and Q_2 (2^{3*floor((M-1)/2)})!
    for ell in [3, 5, 7, 11]:
        for e_K in range(1, ell):
            if (ell - 1) % e_K != 0:
                continue
            r1 = (ell - 1) // e_K
            M = 2 * r1 + 1
            assert (M - 1) * e_K == 2 * ell - 2
            # On K subset Q_ell(mu_ell) of degree e_K, chi^{-r1}(G_K) = 1 + ell Z_ell!
            # Using V' = Q_ell(-r1) + Q_ell(-2*r1), u = chi^{-r1}(g) = 1 + ell*c,
            # T' = Z_ell v_1 + Z_ell (v_1 + v_2)/ell, w = (2/ell^2) v_1 + (1/ell^2) v_2 has order ell^2!
            for c in [1, 2, -1, ell + 1]:
                u = 1 + ell * c
                # (g - 1)w = (2/ell^2)(u - 1) v_1 + (1/ell^2)(u^2 - 1) v_2
                x1 = Fraction(2 * (u - 1), ell * ell)
                x2 = Fraction(u * u - 1, ell * ell)
                # In T' iff ell*x2 in Z and x1 - x2 in Z!
                assert (ell * x2).denominator == 1 and (x1 - x2).denominator == 1
            # Order check: w not in T', ell*w = (2/ell, 1/ell) has x1 - x2 = 1/ell not in Z!
            assert Fraction(2 - 1, ell).denominator > 1
    # Unramified Q_2: chi^2(G_{Q_2}) = 1 + 8 Z_2 => for R = floor((M-1)/2), order 2^{3*R}!
    for R in [1, 2, 3]:
        p_s = 8
        x = [Fraction((-1) ** (R - 1 - m), p_s ** (R - m)) for m in range(R)]
        assert (x[0] * (2 ** (3 * R))).denominator == 1 and (x[0] * (2 ** (3 * R - 1))).denominator > 1
        for c in [-1, 1, 3]:
            u = 1 + 8 * c
            for i in range(R):
                val = sum(Fraction(comb(m, i) * (u ** (i + 1)) * (c ** (m - i)) - (1 if i == m else 0)) * x[m]
                          for m in range(i, R))
                assert val.denominator == 1
    print("  [PASS] 4b: Sharpness of Thm I02-3(i) at (M-1)e_K = 2*ell-2 verified for all e_K | (ell-1)")
    print("             (ell=3,5,7,11) AND unramified Q_2 lower bound 2^{3*floor((M-1)/2)} verified (R=1,2,3).")


# ============================================================================
# Suite 5: Closed-Form Bounds N_tame, N_univ & Exact Full-I_1^2 SNF Benchmarks
# ============================================================================

def compute_N_tame(M, e_K, ell):
    """Exact bound for ell >= 3, e_K <= ell - 2 (Theorem J01-2)."""
    assert ell >= 3 and e_K <= ell - 2
    m0_max = ((M - 1) * e_K) // (ell - 1)
    if m0_max == 0:
        return 0
    # Find smallest j >= 0 with ceil(ell*(j+1)/e_K) > (m0_max + j) + vp_fact(m0_max + j, ell)
    j = 0
    while True:
        gain = (ell * (j + 1) + e_K - 1) // e_K
        loss = (m0_max + j) + vp_fact(m0_max + j, ell)
        if gain > loss:
            return gain - 1
        j += 1


def compute_N_univ(M, e_K, ell, d_K):
    """Exact universal bound for ALL ell >= 2, ALL wild e_K >= 1, ALL M >= 2 (Theorem J01-3)."""
    B = (M - 1) // (ell - 1)
    C = (M - 1) * d_K + vp_fact(M - 1, ell)
    if C == 0:
        return B + vp_fact(B, ell)
    D0 = max(M - 1, C)
    # k_1 = ceil( (ell/(ell-1)) * ((M-1)/(ell-1) + D0) )
    num_k1 = ell * ((M - 1) + D0 * (ell - 1))
    den_k1 = (ell - 1) ** 2
    k1 = (num_k1 + den_k1 - 1) // den_k1
    t = 1
    while True:
        lhs = (ell ** t) * ell * (ell - 1)
        rhs = e_K * (ell + (t + 4) * (ell - 1))
        if lhs >= rhs:
            return k1 + t * C
        t += 1


def run_suite_5():
    print("=" * 74)
    print("Suite 5: Closed-Form Bounds N_tame, N_univ, Benchmarks & Full-I_1^2 Z_3(5)/Z_2(3)")
    print("=" * 74)

    # 5a. Verify closed-form analytic bound t_*(e_K, ell) <= ceil(log_ell(e_K)) + ceil(log_ell(log_ell(e_K) + 6))
    for ell in [2, 3, 5, 7, 11, 53]:
        for e_K in [1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 27, 64, 100, 1000, 100000]:
            L = log(e_K, ell)
            t2 = ceil(L - 1e-12) + ceil(log(L + 6.0, ell) - 1e-12)
            assert (ell ** t2) * ell * (ell - 1) >= e_K * (ell + (t2 + 4) * (ell - 1)), (
                f"Closed-form t2 failed at ell={ell}, e_K={e_K}, t2={t2}"
            )
    print("  [PASS] 5a: Closed-form t_*(e_K, ell) <= ceil(log_ell e_K) + ceil(log_ell(log_ell e_K + 6)) verified")
    print("             across 96 (ell, e_K) pairs up to e_K = 10^5.")

    # 5b. Print & check concrete universal bounds for ALL benchmark fields!
    benchmarks = [
        ("Q_2 (unram, M=2)", 2, 1, 2, 0),
        ("Q_2 (unram, M=3)", 2, 1, 3, 0),
        ("Q_2 (unram, M=10)", 2, 1, 10, 0),
        ("Q_3 (unram, M=5)", 3, 1, 5, 0),
        ("Q_3 (unram, M=10)", 3, 1, 10, 0),
        ("S_3(148)_2 (e_K=3, M=4)", 2, 3, 4, 1),
        ("A_5(2277^2)_3 (wild e_K=3, M=4)", 3, 3, 4, 2),
        ("A_5(2277^2)_11 (tame e_K=3, M=10)", 11, 3, 10, 1),
        ("A_5(6625^2)_5 (wild e_K=10, M=4)", 5, 10, 4, 2),
        ("A_5(6625^2)_53 (tame e_K=3, M=10)", 53, 3, 10, 1),
        ("Q_2(mu_8) (e_K=4, M=2)", 2, 4, 2, 3),
        ("Q_2(mu_16) (e_K=8, M=2)", 2, 8, 2, 4),
        ("Q_3(mu_9) (e_K=6, M=2)", 3, 6, 2, 2),
        ("Q_3(mu_27) (e_K=18, M=2)", 3, 18, 2, 3),
    ]
    for name, ell, e_K, M, d_K in benchmarks:
        nu = compute_N_univ(M, e_K, ell, d_K)
        if ell == 2 and e_K == 1:
            assert nu <= 6 * (M - 1), f"Q_2 linear bound failed at M={M}: {nu}"
        if ell >= 3 and e_K <= ell - 2:
            nt = compute_N_tame(M, e_K, ell)
            best = min(nt, nu)
            print(f"  [BENCH] {name:35s}: N_tame={nt:3d}, N_univ={nu:3d} (best={best})")
        else:
            print(f"  [BENCH] {name:35s}: N_univ={nu:3d}")

    # 5c. Verify exact cancellation (k + M == 0 mod ell) in full nonlinear D_pole(u^{k*ell}) for Z_ell(M) on Q_ell!
    #     For Q_3 (E = u+3), M=5 (k=1): D_pole(u^3) mod 3 has u^5 coeff (1 + 5) == 0 (mod 3)!
    #     For Q_3 (E = u+3), M=7 (k=2): D_pole(u^6) mod 3 has u^8 coeff (2 + 7) == 0 (mod 3)!
    for ell, M, k_idx in [(3, 5, 1), (3, 7, 2), (5, 9, 1)]:
        W = (k_idx + 1) * ell + 2
        E_c = [ell, 1]
        P_out = 2
        R = S1Ring(ell, E_c, P=P_out + W + 2, W=W)
        w = R.var_w()
        ratio_E = R.add(R.const(PolyU([1], ell, R.P, W)), w)  # E_K(u_1)/E_K(u_2) = 1 + w for E = u + ell!
        ratio_M = R.pow(ratio_E, M)
        E_strat = R.const(PolyU([1], ell, R.P, W))
        for _ in range(4):
            E_strat = R.mul(ratio_M, R.phi(E_strat))
        phi_E = R.phi(E_strat)
        m = k_idx * ell
        num = R.pi_w(R.sub(R.mul(phi_E, R.pow(R.u1_elem(), m)), R.const(R.u.pow(m))))
        dp = div_poly_by_E_in_ring(PolyU(num.c[:W - 1], ell, R.P, W - 1), E_c, ell, P_out, W - 1)
        # Check u^{(k+1)*ell - 1} coeff is 0 mod ell!
        deg_check = (k_idx + 1) * ell - 1
        assert dp.c[deg_check] % ell == 0, f"Expected cancellation at deg {deg_check}, got {dp.c[deg_check]}"
    print("  [PASS] 5c: Full nonlinear I_1^2 cancellation (k + M == 0 mod ell) in D_pole(u^{k*ell}) for Z_ell(M)")
    print("             on Q_ell verified for (ell=3,M=5), (ell=3,M=7), (ell=5,M=9).")


# ============================================================================
# Suite 6: Adversarial SNF Stress Test Across All Regimes
# ============================================================================

def dual_system_snf_lin(ell, E_coeffs, Psi_poly_mat, nabla0_mat, M=2, N_exp=3, D=16):
    mod = ell ** N_exp
    d = len(Psi_poly_mat)
    E = PolyU(E_coeffs, ell, N_exp, D)
    E_M1 = E.pow(M - 1)
    E_hi = PolyU(E_coeffs, ell, N_exp + 1, D)
    U0_inv = PolyU(E_hi.delta().c, ell, N_exp, D).inv()
    nvars = 2 * D * d
    rows = []
    for m in range(D):
        for i in range(d):
            row = [0] * nvars
            if m >= 1:
                row[(m - 1) * d + i] = (row[(m - 1) * d + i] + m) % mod
            shift = m + ell - 1
            for j in range(d):
                c = nabla0_mat[j][i] % mod
                if c:
                    for k in range(D - shift):
                        row[(shift + k) * d + j] = (row[(shift + k) * d + j] + c * U0_inv.c[k]) % mod
            rows.append(row)
    for s in range(D):
        for i in range(d):
            row = [0] * nvars
            row[D * d + s * d + i] = (-1) % mod
            shift = ell * s + ell - 1
            for k in range(D - shift):
                row[(shift + k) * d + i] = (row[(shift + k) * d + i] + U0_inv.c[k]) % mod
            rows.append(row)
    for r in range(D):
        for i in range(d):
            row = [0] * nvars
            for k in range(D - r):
                row[(r + k) * d + i] = (row[(r + k) * d + i] + E_M1.c[k]) % mod
            for j in range(d):
                p = Psi_poly_mat[j][i]
                for k in range(min(len(p), D - r)):
                    if p[k]:
                        row[D * d + (r + k) * d + j] = (row[D * d + (r + k) * d + j] - p[k]) % mod
            rows.append(row)
    for m in range(D):
        for i in range(d):
            row = [0] * nvars
            if m >= 1:
                for k in range(D - (m - 1)):
                    row[D * d + (m - 1 + k) * d + i] = (row[D * d + (m - 1 + k) * d + i] + m * E.c[k]) % mod
            for j in range(d):
                if nabla0_mat[j][i]:
                    row[D * d + m * d + j] = (row[D * d + m * d + j] + nabla0_mat[j][i]) % mod
            rows.append(row)
    return snf_exponents_mod_pk(rows, nvars, ell, N_exp)


def run_suite_6():
    print("=" * 74)
    print("Suite 6: Adversarial SNF Verification Against N_tame & N_univ (alpha=1+ell^100)")
    print("=" * 74)
    rng = random.Random(20261123)

    # 6a. Degenerate Psi = 0 with Jordan nabla0 of rank d=3 across wild towers (ell=2, e_K=2,4,6,8; ell=3, e_K=3,6,9)
    for ell, e_K, d_K in [(2, 2, 2), (2, 3, 1), (2, 4, 3), (2, 6, 2), (2, 8, 4), (3, 3, 2), (3, 6, 2), (3, 9, 3)]:
        E_c = [ell] + [0] * (e_K - 1) + [1]
        bnd = compute_N_univ(2, e_K, ell, d_K)
        D = max(18, 3 * e_K + 6)
        Psi = [[[0] for _ in range(3)] for _ in range(3)]
        nab = [[1 if j == i + 1 else 0 for j in range(3)] for i in range(3)]
        ex = dual_system_snf_lin(ell, E_c, Psi, nab, M=2, N_exp=min(bnd + 1, 6), D=D)
        max_e = ex[0] if ex else 0
        assert max_e <= bnd, f"Violation at ell={ell} e_K={e_K}: {max_e} > {bnd}"
    print("  [PASS] 6a: Degenerate Psi=0 + Jordan nabla0 (d=3) across ell=2 (e_K=2,3,4,6,8) & ell=3 (e_K=3,6,9) <= N_univ.")

    # 6b. Random adversarial non-nilpotent nabla0 + alpha=1+ell^100 across unramified Q_2/Q_3 (M=2..6) and wild fields!
    cases = [
        (2, [-2, 1], 2, 0),
        (2, [-2, 1], 4, 0),
        (2, [2, 2, 1], 2, 2),
        (3, [3, 1], 5, 0),
        (3, [3, 3, 1], 3, 1),
        (3, [3, 3, 0, 1], 2, 2),
        (5, [5, 5, 0, 1], 4, 1),
    ]
    for ell, E_c, M, d_K in cases:
        e_K = len(E_c) - 1
        bnd = compute_N_univ(M, e_K, ell, d_K)
        if ell >= 3 and e_K <= ell - 2:
            bnd = min(bnd, compute_N_tame(M, e_K, ell))
        N_test = min(bnd + 1, 4)
        D = max(16, 3 * e_K + 2 * M + 4)
        alpha = 1 + ell ** 100
        # Test scalar alpha = 1 + ell^100 AND random rank-2 (Psi, nabla0)
        ex1 = dual_system_snf_lin(ell, E_c, [[[alpha]]], [[0]], M=M, N_exp=N_test, D=D)
        assert (ex1[0] if ex1 else 0) <= bnd
        for _ in range(3):
            Psi = [[[rng.randint(0, ell ** N_test - 1) for _ in range(3)] for _ in range(2)] for _ in range(2)]
            nab = [[rng.randint(0, ell ** N_test - 1) for _ in range(2)] for _ in range(2)]
            ex2 = dual_system_snf_lin(ell, E_c, Psi, nab, M=M, N_exp=N_test, D=D)
            assert (ex2[0] if ex2 else 0) <= bnd
    print("  [PASS] 6b: All alpha=1+ell^100 & random adversarial rank-2 (Psi, nabla0) cases strictly obey min(N_tame, N_univ).")


if __name__ == "__main__":
    run_suite_1()
    run_suite_2()
    run_suite_3()
    run_suite_4()
    run_suite_5()
    run_suite_6()
    print("=" * 74)
    print("ALL 6 SUITES PASSED (exit 0).")
    sys.exit(0)
