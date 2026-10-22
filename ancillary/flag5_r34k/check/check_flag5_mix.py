#!/usr/bin/env python3
"""Independent exact checker for FIVE-vertex flag certificates with a degree-profile mixture, for a general
t = (t0,t1,t2).  Written from the definitions; it imports nothing from gen/.

Setting.  c is a t-avoiding 3-colouring of K_n (no colour-i K_{t_i}).  Lemma 2.1: d_i(v) <= D_i = R(t - e_i) - 1,
so every vertex profile d(v) = (d_0, d_1, d_2) is admissible: d_i <= D_i, sum n - 1.

Random object.  (x0,...,x4) a uniform ordered 5-tuple of distinct vertices and an independent uniform sigma in
Gt (colour permutations preserving t); P = the colours of the ten pairs under sigma o c.  The law of P is
invariant under S_5 x Gt, so E[F(P)] = E[Sym F(P)] for every F; Sym F is the mean of F over the orbit.

Terms (all constants recomputed here):
  star   G = sum_s y_s 1[(c01,c02,c03,c04) = s],  E[G] = (1/n) sum_v J(sigma d(v)) <= max_{d admissible} J(d),
         J(d) = sum_s y_s d_{s0}(d_{s1}-[s1=s0])(d_{s2}-#{l<2: s_l=s2})(d_{s3}-#{l<3: s_l=s3}) / (n-1)_4.
  rows on the roots x0..x3, new vertex x4, nf = n - 4, rho = colours of (01,02,03,12,13,23):
   'up'  (rho,j,c): 1[rho] (1[c(x_j x4)=c] - (D_c - deg)/nf)                      E <= 0
   'low' (rho,j,c): 1[rho] ((Lo_c - deg)/nf - 1[c(x_j x4)=c]),  Lo_c = n-1-sum_{c'!=c} D_c'   E <= 0
         deg = #{roots l != j : rho(j,l) = c}.
   'int' (rho,J,a): 1[rho] (1[c(x_j x4) = a_j, j in J] - q/nf),  S = {y : c(x_j y) = a_j, j in J};
         w_i = largest colour-i clique (in rho) among {x_j : j in J, a_j = i}; a colour-i clique in S plus that
         clique is a colour-i clique, so S is (t-w)-avoiding and |S| <= R(t-w) - 1; the roots l not in J lying
         in S are subtracted: q = R(t-w) - 1 - #{l not in J : rho(l,j) = a_j for all j in J}.   E <= 0.
  squares (block: k0 roots x0..x_{k0-1} with root pattern tau; basis of pairs (e, key)):
         for roots r and an ordered e-tuple Y of distinct non-roots, key(r;Y) lists, for each y in Y in order,
         its colours to roots 0..k0-1, then the colours of the pairs (y_i,y_j), i<j.  f_b(r) = mean over Y of
         1[key(r;Y) = key_b].  The square term is 1[tau] lam (sum_b v_b f_b(r))^2 >= 0.  Its expectation is the
         expectation of the following function of P (exact expansion of the product of two means over tuples
         A, B, by the overlap pattern om of B with A; M = n - k0, (M)_k falling factorial):
           Q(P) = 1[tau] sum_{e_a, e_b} sum_om (M)_{e_a + new(om)} / ((M)_{e_a} (M)_{e_b})
                        * Yq[(e_a, key(r; A)), (e_b, key(r; B_om))],     Yq = lam v v^T,
         with A at positions k0..k0+e_a-1 and the new vertices of B at the next positions (needs
         k0 + e_a + e_b <= 5).  (For each ordered pair of tuples (A,B) with overlap om, the joint law of
         (r, A, B) is that of (r, the vertices at those positions) under the uniform 5-tuple.)
Certificate: z >= 0 on rows, lam >= 0, any y.  F = G + sum z row - sum Q.  Valid iff
   min over valid labelled patterns of Sym F  >  max over admissible d of J(d).
Then E[F] <= E[G] <= max J < min Sym F <= E[Sym F] = E[F], a contradiction: no t-avoiding colouring of K_n.
"""
import json, sys
from fractions import Fraction as Fr
from itertools import permutations, product, combinations

PAIRS = list(combinations(range(5), 2))
PIDX = {p: i for i, p in enumerate(PAIRS)}

R2 = {(3, 3): 6, (3, 4): 9, (3, 5): 14, (3, 6): 18, (3, 7): 23, (3, 8): 28, (3, 9): 36, (3, 10): 41,
      (4, 4): 18, (4, 5): 25, (4, 6): 41, (4, 7): 61, (4, 8): 84, (5, 5): 46, (5, 6): 87}      # published
R3_BASE = {(3, 3, 3): 17, (3, 3, 4): 30, (3, 3, 5): 57, (3, 4, 4): 77, (3, 3, 6): 88, (3, 4, 5): 155,
           (3, 3, 7): 129, (3, 3, 8): 179, (3, 4, 6): 276, (3, 5, 5): 346, (3, 4, 7): 458}
# GG55, CFIM16, recurrence (3,3,5),(3,4,4); the paper's theorems for (3,3,6),(3,3,7),(3,3,8),(3,4,5),(3,4,6),
# (3,5,5) and Proposition 6.5 (no starred inputs) for (3,4,7).  Other inputs only via --input.


def make_ramsey(extra):
    t3 = dict(R3_BASE); t2 = dict(R2)
    for k, v in extra.items():
        k = tuple(sorted(k))
        if len(k) == 2:
            assert k in t2 and v <= t2[k]; t2[k] = v
        else:
            assert len(k) == 3 and k[0] >= 3 and v <= t3.get(k, 10 ** 9); t3[k] = v
    used = {}

    def R(s):
        s = tuple(sorted(s))
        assert s[0] >= 1
        if s[0] == 1:
            return 1
        if s[0] == 2:
            if s[1] == 1:
                return 1
            if s[1] == 2:
                return s[2]
            used[(s[1], s[2])] = t2[(s[1], s[2])]
            return t2[(s[1], s[2])]
        used[s] = t3[s]
        return t3[s]
    R.used = used
    return R


def ff(M, k):
    v = 1
    for i in range(k):
        v *= M - i
    return v


def overlaps(ea, eb):
    out = []
    def rec(i, used, cur):
        if i == eb:
            out.append(tuple(cur)); return
        rec(i + 1, used, cur + [-1])
        for a in range(ea):
            if a not in used:
                rec(i + 1, used | {a}, cur + [a])
    rec(0, frozenset(), [])
    return out


def build_terms(cert, extra=None):
    """Returns a dict with F (function of a labelled 5-pattern p, a tuple over PAIRS), J, profs, D, valid, gmaps,
    R (the Ramsey lookup, with .used), extra, and row_q(kind, rho, J, a) (the recomputed constant)."""
    t = tuple(cert['t']); n = int(cert['n']); extra = dict(extra or {})
    R = make_ramsey(extra)
    D = [R([t[k] - (k == i) for k in range(3)]) - 1 for i in range(3)]
    if 'D' in cert:
        assert list(cert['D']) == D, ('degree caps mismatch', cert['D'], D)
    profs = [(a, b, n - 1 - a - b) for a in range(D[0] + 1) for b in range(D[1] + 1) if 0 <= n - 1 - a - b <= D[2]]
    Gt = [s for s in permutations(range(3)) if all(t[s[c]] == t[c] for c in range(3))]
    nf = n - 4

    def c4(rho, i, j):   # rho on pairs (01,02,03,12,13,23)
        if i > j:
            i, j = j, i
        return rho[[(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)].index((i, j))]

    def clique(vs, rho, c):
        for r in range(len(vs), 0, -1):
            for S in combinations(vs, r):
                if all(c4(rho, a, b) == c for a, b in combinations(S, 2)):
                    return r
        return 0

    # ---- stars
    ys = {}
    for s in cert['stars']:
        key = tuple(s['star']); assert len(key) == 4 and key not in ys
        ys[key] = Fr(s['mult'])
    # ---- rows
    def row_q(kind, rho, J, a):
        assert len(rho) == 6 and len(J) == len(a) and len(set(J)) == len(J) and all(0 <= j < 4 for j in J)
        if kind == 'int':
            assert len(J) >= 1
            w = [clique([j for j, aj in zip(J, a) if aj == i], rho, i) for i in range(3)]
            s = [t[i] - w[i] for i in range(3)]
            assert min(s) >= 1, 'root pattern with a forbidden clique'
            known = sum(1 for l in range(4) if l not in J and all(c4(rho, l, j) == aj for j, aj in zip(J, a)))
            return R(s) - 1 - known
        assert kind in ('up', 'low') and len(J) == 1
        j, c = J[0], a[0]
        deg = sum(1 for l in range(4) if l != j and c4(rho, j, l) == c)
        return (D[c] - deg) if kind == 'up' else (n - 1 - sum(D) + D[c] - deg)

    rows = {}
    for r in cert['rows']:
        kind, rho, J, a, z = r['kind'], tuple(r['rho']), tuple(r['J']), tuple(r['a']), Fr(r['mult'])
        assert z >= 0
        q = row_q(kind, rho, J, a)
        assert int(r['q']) == q, ('constant mismatch', r, q)
        rows.setdefault(rho, []).append((kind, J, a, z, Fr(q, nf)))
    # ---- squares: accumulate Yq = sum lam v v^T per block (k0, tau, basis)
    blocks = {}
    for s in cert['squares']:
        k0 = int(s['k0']); tau = tuple(s['tau']); lam = Fr(s['lam'])
        assert lam >= 0 and k0 in (1, 2, 3) and len(tau) == k0 * (k0 - 1) // 2
        basis = [tuple(b) for b in s['basis']]
        for b in basis:
            e = b[0]
            assert len(b) - 1 == e * k0 + e * (e - 1) // 2
        es = sorted(set(b[0] for b in basis))
        assert k0 + 2 * max(es) <= 5, 'block needs more than five vertices'
        assert len(s['vec']) == len(basis) and len(set(basis)) == len(basis)
        bk = (k0, tau)
        Y = blocks.setdefault(bk, {})
        vec = [Fr(v) for v in s['vec']]
        for b1, v1 in zip(basis, vec):
            if v1 == 0:
                continue
            for b2, v2 in zip(basis, vec):
                if v2 == 0:
                    continue
                Y[(b1, b2)] = Y.get((b1, b2), Fr(0)) + lam * v1 * v2
    bl = []
    for (k0, tau), Y in blocks.items():
        es = sorted(set(b[0][0] for b in Y))
        M = n - k0
        terms = []
        for ea in es:
            for eb in es:
                A = list(range(k0, k0 + ea))
                for om in overlaps(ea, eb):
                    nxt = k0 + ea; B = []
                    for x in om:
                        if x >= 0:
                            B.append(A[x])
                        else:
                            B.append(nxt); nxt += 1
                    assert nxt <= 5
                    new = sum(1 for x in om if x < 0)
                    terms.append((ea, eb, tuple(A), tuple(B), Fr(ff(M, ea + new), ff(M, ea) * ff(M, eb))))
        bl.append((k0, tau, Y, terms))

    def col(p, i, j):
        return p[PIDX[(min(i, j), max(i, j))]]

    def key(p, k0, pos):
        k = []
        for y in pos:
            for r in range(k0):
                k.append(col(p, r, y))
        for i in range(len(pos)):
            for j in range(i + 1, len(pos)):
                k.append(col(p, pos[i], pos[j]))
        return tuple(k)

    def roots_pattern(p, k0):
        return tuple(col(p, i, j) for i, j in combinations(range(k0), 2))

    def F(p):
        v = ys.get((col(p, 0, 1), col(p, 0, 2), col(p, 0, 3), col(p, 0, 4)), Fr(0))
        rho = (col(p, 0, 1), col(p, 0, 2), col(p, 0, 3), col(p, 1, 2), col(p, 1, 3), col(p, 2, 3))
        for kind, J, a, z, qq in rows.get(rho, ()):
            ev = 1 if all(col(p, j, 4) == aj for j, aj in zip(J, a)) else 0
            v += z * ((ev - qq) if kind != 'low' else (qq - ev))
        for k0, tau, Y, terms in bl:
            if roots_pattern(p, k0) != tau:
                continue
            for ea, eb, A, B, cf in terms:
                y = Y.get(((ea,) + key(p, k0, A), (eb,) + key(p, k0, B)))
                if y:
                    v -= cf * y
        return v

    def valid(p):
        for c in range(3):
            for S in combinations(range(5), t[c]):
                if all(col(p, a, b) == c for a, b in combinations(S, 2)):
                    return False
        return True

    # group S5 x Gt acting on labelled patterns
    gmaps = []
    for pi in permutations(range(5)):
        dst = [PIDX[(min(pi[i], pi[j]), max(pi[i], pi[j]))] for (i, j) in PAIRS]
        for s in Gt:
            gmaps.append((dst, s))

    def act(p, g):
        dst, s = g
        q = [0] * 10
        for k in range(10):
            q[dst[k]] = s[p[k]]
        return tuple(q)

    den = ff(n - 1, 4)

    def J(d):
        tot = Fr(0)
        for s, y in ys.items():
            dd = list(d); v = 1
            for c in s:
                v *= dd[c]; dd[c] -= 1
            tot += y * v
        return tot / den
    return dict(F=F, J=J, profs=profs, D=D, valid=valid, gmaps=gmaps, act=act, R=R, extra=extra, row_q=row_q,
                t=t, n=n, Gt=Gt, nblocks=len(bl))


def check(path, extra=None, verbose=True):
    cert = json.load(open(path))
    B = build_terms(cert, extra)
    F, J, profs, D, valid, gmaps, act, R, extra = (B[k] for k in ('F', 'J', 'profs', 'D', 'valid', 'gmaps', 'act', 'R', 'extra'))
    t, n = B['t'], B['n']
    seen = set(); worst = None; norb = 0; nvalid = 0
    for p in product(range(3), repeat=10):
        if p in seen or not valid(p):
            continue
        orb = {act(p, g) for g in gmaps}
        seen |= orb
        nvalid += len(orb); norb += 1
        val = sum((F(q) for q in orb), Fr(0)) / len(orb)
        worst = val if worst is None or val < worst else worst
    Jmax = max(J(d) for d in profs) if profs else None
    ok = (not profs) or worst > Jmax
    if verbose:
        us = sorted(R.used.items(), key=lambda kv: (len(kv[0]), kv[0]))
        print('  Ramsey inputs looked up: ' + ', '.join(f'R{k}<={v}{" [input]" if tuple(sorted(k)) in extra else ""}' for k, v in us))
        print(f'{path}: t={t} n={n} D={tuple(D)}; {len(profs)} admissible profiles; {len(cert["stars"])} stars, {len(cert["rows"])} rows, '
              f'{len(cert["squares"])} squares in {B["nblocks"]} blocks; {nvalid} valid labelled 5-patterns in {norb} orbits; '
              f'min Sym F - max J = {float(worst - Jmax) if profs else "n/a"} -> {"VALID" if ok else "INVALID"}')
    return ok


if __name__ == '__main__':
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('certs', nargs='+')
    ap.add_argument('--input', action='append', default=[], help='extra bound, e.g. 3,4,4:74 or 4,7:58')
    args = ap.parse_args()
    extra = {}
    for item in args.input:
        k, v = item.split(':'); extra[tuple(sorted(int(x) for x in k.split(',')))] = int(v)
    res = [check(p, extra) for p in args.certs]
    print('ALL VALID' if all(res) else 'SOME INVALID')
    sys.exit(0 if all(res) else 1)
