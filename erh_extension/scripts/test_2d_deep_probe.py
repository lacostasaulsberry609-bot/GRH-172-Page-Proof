#!/usr/bin/env python3
"""
Wave-3 Assault A01 (Part 4): Deep Probe of:
1. Restriction of T_{f, M} to unit-invariant functions Phi(eps_+ * x) = Phi(omega * x) = Phi(-x) = Phi(x) mod f:
   - Does f^2 cancel COMPLETELY in S_Phi(u)? (Explaining den_lcm = 1 even when l | f!)
   - What is the exact rank mod l INCLUDING when l | f?!
2. Sparse dual vector search: Is there a sparse / structured linear combination sum_u c(u) S_Phi(u)
   that isolates Phi(1) = 1?
3. FULL GSp4 admissibility test on F^+_725 and F^CM_1025 for l = 3, 5, 7, 11:
   - Check ALL 6 Raw.Good conditions simultaneously for prime-to-l totally odd ray-class chars xi!
"""

import math
from fractions import Fraction
import sympy as sp
from test_2d_rayclass_corx import mul_ok, norm_ok, compute_GM_table, make_psi0_725, make_psi0_1025
from test_2d_rank_killer import gf_rank

def test_unit_invariant_subspace():
    print("=" * 72)
    print("PROBE 1: T_{f, M} ON UNIT-INVARIANT SUBSPACE (Phi(u*x) = Phi(x) for u in O_K0^x)")
    print("         CHECKING DENOMINATOR CANCELLATION & RANK WHEN l | f !!")
    print("=" * 72)
    # A totally even ray-class function mod f*O_K0 satisfies:
    #   Phi(a, b) = 0 if gcd(N(a, b), f) > 1? (Wait: for imprimitive/split f, maybe nonzero on one prime!)
    #   More generally, ANY totally even function on O_K0 / f O_K0 satisfies:
    #   Phi(x * u) = Phi(x) for all u in <-1, omega> (including eps_+ = omega^2)!
    #   AND row sums = 0, col sums = 0!
    for f, M in [(7, 55), (11, 55), (13, 55), (15, 61), (21, 55), (29, 55), (7, 144), (11, 144)]:
        if math.gcd(f, M) != 1:
            continue
        # Find orbits of H_f = <-1, omega> acting on (Z/fZ)^2 (all pairs, not just units!)
        eps_f = (0, 1 % f)
        om_f = ((-1) % f, 1 % f)
        neg1_f = ((-1) % f, 0)
        # Generate H_f
        H_f = set()
        cur = (1 % f, 0)
        while cur not in H_f:
            H_f.add(cur)
            cur = mul_ok(cur, om_f, f)
        H_f_full = set(H_f) | set(mul_ok(neg1_f, h, f) for h in H_f)

        visited = set()
        orbits = []
        for a in range(f):
            for b in range(f):
                if (a, b) in visited:
                    continue
                orb = sorted(set(mul_ok((a, b), h, f) for h in H_f_full))
                for pt in orb:
                    visited.add(pt)
                orbits.append(orb)

        # Build the indicator matrix of orbits, and find the subspace of orbit-constant functions
        # with ALL row sums = 0 and ALL col sums = 0!
        # Wait: let's just build the exact basis of {c in Q^{#orbits} : row_sums = 0, col_sums = 0}
        n_orb = len(orbits)
        # Constraint matrix: 2f rows (f row sums, f col sums), n_orb cols
        cons = sp.zeros(2 * f, n_orb)
        for j, orb in enumerate(orbits):
            for a, b in orb:
                cons[a, j] += 1
                cons[f + b, j] += 1
        ns = cons.nullspace()
        dim_sub = len(ns)
        if dim_sub == 0:
            print(f"  f={f:2d}, M={M:3d}: #H_f-orbits={n_orb}, dim(row/col=0 subspace) = 0")
            continue

        # Clear denominators in nullspace basis vectors (make primitive integer vectors)
        basis_vecs = []
        for v in ns:
            den = 1
            for x in v:
                den = math.lcm(den, int(x.q))
            iv = [int(x * den) for x in v]
            g = 0
            for x in iv:
                g = math.gcd(g, x)
            iv = [x // g for x in iv]
            basis_vecs.append(iv)

        # Compute exact S_Phi(u) for each basis vector!
        # First get cosets of H_M in U_M
        units = [(a, b) for a in range(M) for b in range(M) if math.gcd(norm_ok((a, b)), M) == 1]
        eps_M = (0, 1 % M)
        om_M = ((-1) % M, 1 % M)
        neg1_M = ((-1) % M, 0)
        E_M = []
        cur = (1 % M, 0)
        while True:
            E_M.append(cur)
            cur = mul_ok(cur, eps_M, M)
            if cur == (1 % M, 0):
                break
        E_pm = list(set(E_M) | set(mul_ok(neg1_M, e, M) for e in E_M))
        wE_pm = [mul_ok(om_M, e, M) for e in E_pm]
        visM = set()
        cosets = []
        for u in units:
            if u in visM: continue
            pos_pts = [mul_ok(u, e, M) for e in E_pm]
            neg_pts = [mul_ok(u, e, M) for e in wE_pm]
            for x in pos_pts: visM.add(x)
            for x in neg_pts: visM.add(x)
            pos_1 = [(x[0] if x[0] > 0 else M, x[1] if x[1] > 0 else M) for x in pos_pts]
            neg_1 = [(x[0] if x[0] > 0 else M, x[1] if x[1] > 0 else M) for x in neg_pts]
            cosets.append((pos_1, neg_1))

        Minv = pow(M, -1, f)
        import numpy as np
        y_arr = np.arange(f, dtype=np.int64)
        R_mat = ((y_arr[None, :] - y_arr[:, None]) * Minv) % f

        # Build matrix cols: each basis vec -> S_Phi(u) as exact Fraction!
        # Check LCM of denominators across ALL basis vecs!
        den_lcm = 1
        frac_cols = []
        for bv in basis_vecs:
            phi_tab = np.zeros((f, f), dtype=np.int64)
            for j, orb in enumerate(orbits):
                val = bv[j]
                if val:
                    for a, b in orb:
                        phi_tab[a, b] = val
            S11 = R_mat @ phi_tab @ R_mat.T
            col = []
            for pos_1, neg_1 in cosets:
                s = 0
                for a, b in pos_1:
                    s += int(S11[a % f, b % f])
                for a, b in neg_1:
                    s -= int(S11[a % f, b % f])
                fr = Fraction(s, f * f)
                den_lcm = math.lcm(den_lcm, fr.denominator)
                col.append(fr)
            frac_cols.append(col)

        # Convert to integer matrix (multiplying by den_lcm)
        mat = [[int(frac_cols[c][r] * den_lcm) for c in range(dim_sub)] for r in range(len(cosets))]
        # Test rank mod ALL prime divisors of f AND mod 3, 5, 7, 11, 101!
        test_ps = sorted(set(list(sp.factorint(f).keys()) + [3, 5, 7, 101]))
        ranks = {}
        for p in test_ps:
            if p == 2: continue
            if den_lcm % p == 0:
                ranks[f"{p}(den!)"] = "den_div"
            else:
                ranks[p] = gf_rank(mat, p)
        print(f"  f={f:2d}, M={M:3d} (N_cos={len(cosets):3d}): unit-inv dim={dim_sub:2d}, den_lcm={den_lcm}, ranks={ranks}")

def test_sparse_dual():
    print("\n" + "=" * 72)
    print("PROBE 2: SEARCHING FOR SPARSE DUAL VECTORS c(u) AT f=7, M=55 AND f=5, M=144")
    print("=" * 72)
    # For f = 7, M = 55: unit-inv subspace has small dim! Let's check exact values of S_Phi on cosets
    # and see if a tiny subset of cosets (say size dim_sub) already has full rank!
    f, M = 7, 55
    eps_f = (0, 1 % f)
    om_f = ((-1) % f, 1 % f)
    neg1_f = ((-1) % f, 0)
    H_f = set()
    cur = (1 % f, 0)
    while cur not in H_f:
        H_f.add(cur)
        cur = mul_ok(cur, om_f, f)
    H_f_full = set(H_f) | set(mul_ok(neg1_f, h, f) for h in H_f)
    visited = set()
    orbits = []
    for a in range(f):
        for b in range(f):
            if (a, b) in visited: continue
            orb = sorted(set(mul_ok((a, b), h, f) for h in H_f_full))
            for pt in orb: visited.add(pt)
            orbits.append(orb)
    print(f"  f=7 orbits of <-1, omega> on (Z/7Z)^2: {len(orbits)} orbits, sizes = {[len(o) for o in orbits]}")
    for idx, o in enumerate(orbits):
        print(f"    orbit {idx} (size {len(o)}, norm mod 7 = {norm_ok(o[0])%7}): sample {o[:4]}")

def test_gsp4_full_admissibility():
    print("\n" + "=" * 72)
    print("PROBE 3: FULL GSp4 ADMISSIBILITY (ALL 6 Raw.Good CONDITIONS!) ON F^+_725 & F^CM_1025")
    print("=" * 72)
    # Check for F^+_725 (f = 29, psi_0 even) and l = 3, 5, 7, 11 with e = l-1 (so omega^e = 1, Case IIb)
    # AND l = 3, e = 1 on F^CM_1025 (phi = chi_3 o N * psi_0^CM, f = 123, l | f!)
    # Conditions for xi in Cl^+_{M O_K0}(K0) to be 100% GSp4-admissible:
    # 1. Totally odd: xi(-1) = 1, xi(omega) = -1
    # 2. Prime-to-l order: l not| ord(xi)
    # 3. condD at v | l: for ALL i in Z, bar(xi * Psi^i)(Frob_v) != 1
    #    Note: Since Psi = psi_0 (of order 2) at e = l-1, Psi^i in {1, psi_0}, so we need:
    #      bar(xi)(Frob_v) != 1  AND  bar(xi * psi_0)(Frob_v) != 1  for ALL v | l!
    #    WAIT: in Q(sqrt(5)):
    #      - l = 3 (inert): Frob_v = (3) = principal ideal (3), so xi(Frob_v) = xi(3)!
    #      - l = 5 (ramified): p_5 = (sqrt(5)) = (2*eps_+ - 3) = (-3, 2) [Wait: N(-3+2e) = 9-18+4 = -5, so totally pos gen is omega*(-3+2e)!]
    #      - l = 7 (inert): Frob_v = (7)!
    #      - l = 11 (split): 11 = p_11 * p_11', generators alpha_1, alpha_2 totally positive of norm 11!
    # 4. bigL at v | l: bar(xi)(Frob_v)^4 != 1 for ALL v | l! (Note: implies condD for order-2 psi_0 automatically!)
    # 5. big2 at SOME prime q | M: bar(xi)(I_q)^4 != 1 (i.e. restriction of xi to (O/q)^x has order > 4!)
    # 6. Triple nonvanishing: L(0, xi^{-1}), L(0, phi^{-1}*xi), L(0, phi^{-1}*xi^{-1}) ALL != 0 mod P!
    #
    # Let's check M = 17, 31, 41, 55, 61 for F^+_725 at l = 3, 5, 7, 11!
    f, phi = make_psi0_725()

    # Totally positive generators of primes above l = 3, 5, 7, 11 in K0 = Q(sqrt(5)):
    # l = 3 (inert): (3, 0), N = 9 > 0, totally pos!
    # l = 5 (ramified): omega * (2*eps_+ - 3) = (-1, 1)*(-3, 2) = (3 - 2, -2 - 3 + 6) = (1, 1) -> 1 + eps_+!
    #   Check: N(1 + eps_+) = 1 + 3 + 1 = 5! Both embeddings: 1 + 2.618 > 0 and 1 + 0.382 > 0! TOTALLY POSITIVE!
    # l = 7 (inert): (7, 0), totally pos!
    # l = 11 (split): need a + b*eps_+ totally pos with a^2 + 3ab + b^2 = 11!
    #   Try b = 1: a^2 + 3a + 1 = 11 => a^2 + 3a - 10 = 0 => (a+5)(a-2) = 0 => a = 2!
    #   Check (2, 1): 2 + eps_+ > 0 at both embeddings (2+2.618, 2+0.382)! N = 4 + 6 + 1 = 11!
    #   Conjugate: 2 + eps_+^{-1} = 2 + (3 - eps_+) = (5, -1)! Check: 5 - 2.618 > 0, 5 - 0.382 > 0, N = 25-15+1 = 11!
    frob_gens = {
        3: [(3, 0)],
        5: [(1, 1)],
        7: [(7, 0)],
        11: [(2, 1), (5, -1)],
    }
    for l_p, gens in frob_gens.items():
        for g in gens:
            assert norm_ok(g) in (l_p, l_p * l_p)

    for M in [31, 41, 55, 61]:
        # Build Cl^+_M and test ALL 6 conditions!
        units = [(a, b) for a in range(M) for b in range(M) if math.gcd(norm_ok((a, b)), M) == 1]
        eps = (0, 1 % M)
        omega = ((-1) % M, 1 % M)
        neg1 = ((-1) % M, 0)
        E_M = []
        cur = (1 % M, 0)
        while True:
            E_M.append(cur)
            cur = mul_ok(cur, eps, M)
            if cur == (1 % M, 0): break
        E_pm = list(set(E_M) | set(mul_ok(neg1, e, M) for e in E_M))
        wE_pm = [mul_ok(omega, e, M) for e in E_pm]

        G_phi, denom_phi = compute_GM_table(f, phi, M)
        G_triv, denom_triv = compute_GM_table(1, lambda a, b: 1, M)

        visited = set()
        coset_reps = []
        S_phi_list = []
        S_triv_list = []
        for u in units:
            if u in visited: continue
            coset_reps.append(u)
            sp_v = st_v = 0
            for e in E_pm:
                x = mul_ok(u, e, M)
                visited.add(x)
                sp_v += G_phi[x[0]][x[1]]
                st_v += G_triv[x[0]][x[1]]
            for e in wE_pm:
                x = mul_ok(u, e, M)
                visited.add(x)
                sp_v -= G_phi[x[0]][x[1]]
                st_v -= G_triv[x[0]][x[1]]
            S_phi_list.append(Fraction(sp_v, denom_phi))
            S_triv_list.append(Fraction(st_v, denom_triv))

        # Abelian decomposition of Cl^+_M
        elem_to_class = {}
        class_reps = []
        for u in units:
            if u in elem_to_class: continue
            cid = len(class_reps)
            class_reps.append(u)
            for e in E_M:
                elem_to_class[mul_ok(u, e, M)] = cid
        G_n = len(class_reps)
        id_cls = elem_to_class[(1 % M, 0)]
        def g_mul(i, j): return elem_to_class[mul_ok(class_reps[i], class_reps[j], M)]
        def g_pow(i, k):
            res = id_cls
            base = i
            while k > 0:
                if k & 1: res = g_mul(res, base)
                base = g_mul(base, base)
                k >>= 1
            return res

        fac = sp.factorint(G_n)
        all_gens = []
        for p_f, exp in sorted(fac.items()):
            cof = G_n // (p_f ** exp)
            syl = sorted(set(g_pow(i, cof) for i in range(G_n)))
            sub_coords = {id_cls: ()}
            basis = []
            while len(sub_coords) < len(syl):
                best_x, best_k = None, 0
                for x in syl:
                    if x in sub_coords: continue
                    cur_x, k = x, 0
                    while cur_x not in sub_coords:
                        cur_x = g_pow(cur_x, p_f)
                        k += 1
                    if k > best_k: best_k, best_x = k, x
                pk = p_f ** best_k
                t_coords = sub_coords[g_pow(best_x, pk)]
                adj = best_x
                for (gj, oj), cj in zip(basis, t_coords):
                    adj = g_mul(adj, g_pow(gj, (-(cj // pk)) % oj))
                new_sub = {}
                cp = id_cls
                for a in range(pk):
                    for el, co in sub_coords.items():
                        new_sub[g_mul(el, cp)] = co + (a,)
                    cp = g_mul(cp, adj)
                sub_coords = new_sub
                basis.append((adj, pk))
            all_gens.extend(basis)

        cur_set = {id_cls: ()}
        for gj, oj in all_gens:
            nxt = {}
            cp = id_cls
            for a in range(oj):
                for el, co in cur_set.items():
                    nxt[g_mul(el, cp)] = co + (a,)
                cp = g_mul(cp, gj)
            cur_set = nxt
        coords = cur_set
        ords = [o for _, o in all_gens]
        coset_coords = [coords[elem_to_class[u]] for u in coset_reps]
        w_coords = coords[elem_to_class[omega]]
        m1_coords = coords[elem_to_class[neg1]]

        # Inertia elements at prime factors of M (for big2: xi(u)^4 != 1 for some u == 1 mod M/q^a)
        # Note: if M is prime, EVERY u in U is in inertia I_M (mod M = q) so big2 just means ord(xi) > 4!
        # Even better: for split prime q | M, check inertia at q1 (elements == 1 mod q2)!
        print(f"\n  MODULUS M = {M}:")
        for l in [3, 5, 7, 11]:
            if M % l == 0: continue
            pl_ords = []
            for o in ords:
                rem = o
                while rem % l == 0: rem //= l
                pl_ords.append(rem)
            E_l = 1
            for ro in pl_ords: E_l = math.lcm(E_l, ro)
            valid_vs = []
            def rec(idx, cur_v):
                if idx == len(pl_ords):
                    if sum(Fraction(cur_v[j] * m1_coords[j], pl_ords[j]) for j in range(len(pl_ords))).denominator != 1:
                        return
                    if (sum(Fraction(cur_v[j] * w_coords[j], pl_ords[j]) for j in range(len(pl_ords))) - Fraction(1, 2)).denominator != 1:
                        return
                    valid_vs.append(tuple(cur_v))
                    return
                for val in range(pl_ords[idx]):
                    cur_v.append(val)
                    rec(idx + 1, cur_v)
                    cur_v.pop()
            rec(0, [])
            if not valid_vs:
                continue

            # Frob_v coords for v | l
            frob_cs = [coords[elem_to_class[(g[0] % M, g[1] % M)]] for g in frob_gens[l]]

            # Build F_{l^d}
            d_ext = 1
            cp = l % E_l
            while cp != 1:
                cp = (cp * l) % E_l
                d_ext += 1
            x_sym = sp.Symbol('x')
            if d_ext == 1:
                prim_root = next(g for g in range(1, l)
                                 if pow(g, E_l, l) == 1 and all(pow(g, E_l // p_q, l) != 1 for p_q in sp.factorint(E_l)))
                zpow = [[pow(prim_root, k, l)] for k in range(E_l)]
            else:
                phi_poly = sp.Poly(sp.cyclotomic_poly(E_l, x_sym), x_sym, modulus=l)
                irr = [int(c) % l for c in reversed(sp.factor_list(phi_poly, modulus=l)[1][0][0].all_coeffs())]
                zpow = [[0] * d_ext for _ in range(E_l)]
                zpow[0][0] = 1
                for k in range(1, E_l):
                    prev = zpow[k - 1]
                    top = prev[d_ext - 1]
                    nxt = [(-top * irr[0]) % l] + [(prev[j - 1] - top * irr[j]) % l for j in range(1, d_ext)]
                    zpow[k] = nxt

            Sp_mod = [(x.numerator * pow(x.denominator, -1, l)) % l for x in S_phi_list]
            St_mod = [(x.numerator * pow(x.denominator, -1, l)) % l for x in S_triv_list]

            # Check ALL 6 conditions!
            cnt_all3 = 0
            cnt_full_gsp4 = 0
            cnt_full_noncyc = 0
            for v in valid_vs:
                # 1. Check bigL (which implies condD for order-2 psi_0): xi(Frob_v)^4 != 1 for all v | l
                ok_bigL = True
                for fc in frob_cs:
                    e_f = sum(v[j] * fc[j] * (E_l // pl_ords[j]) for j in range(len(pl_ords))) % E_l
                    if (4 * e_f) % E_l == 0:
                        ok_bigL = False
                        break
                # 2. Check big2: ord(xi) > 4 (for prime M, inertia = U; for M=55=5*11, check inertia at 11)
                ord_xi = 1
                for j in range(len(pl_ords)):
                    if v[j] != 0:
                        ord_xi = math.lcm(ord_xi, pl_ords[j] // math.gcd(pl_ords[j], v[j]))
                ok_big2 = (ord_xi > 4)
                # Check if xi is genuinely NON-CYCLOTOMIC (does NOT factor through norm N_{K0/Q}):
                # Find an element of norm 1 mod M not in E_M, check if xi(u) != 1!
                is_noncyc = False
                for u_c, cc in zip(coset_reps, coset_coords):
                    if norm_ok(u_c) % M == 1:
                        e_n = sum(v[j] * cc[j] * (E_l // pl_ords[j]) for j in range(len(pl_ords))) % E_l
                        if e_n != 0:
                            is_noncyc = True
                            break

                # 3. Evaluate L-values
                vp1 = [0] * d_ext
                vp2 = [0] * d_ext
                vt = [0] * d_ext
                for idx_c, cc in enumerate(coset_coords):
                    e = sum(v[j] * cc[j] * (E_l // pl_ords[j]) for j in range(len(pl_ords))) % E_l
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
                if any(vt) and any(vp1) and any(vp2):
                    cnt_all3 += 1
                    if ok_bigL and ok_big2:
                        cnt_full_gsp4 += 1
                        if is_noncyc:
                            cnt_full_noncyc += 1
            nv = len(valid_vs)
            print(f"    l={l:2d}: #xi={nv:2d}, ALL3={cnt_all3:2d}, FULL_GSp4(ALL3+bigL+big2)={cnt_full_gsp4:2d}, "
                  f"of which GENUINE_2D_NONCYCLOTOMIC={cnt_full_noncyc:2d}")

if __name__ == "__main__":
    test_unit_invariant_subspace()
    test_sparse_dual()
    test_gsp4_full_admissibility()
