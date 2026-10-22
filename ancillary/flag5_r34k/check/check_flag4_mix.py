#!/usr/bin/env python3
"""Independent exact checker for four-vertex flag certificates with a degree-profile mixture
(Section 7 of the paper, for a general t = (t0,t1,t2)); written from the definitions, no code shared with gen/.

A t-avoiding colouring c of K_n (no colour-i K_{t_i}).  Lemma 2.1: d_i(v) <= D_i := R(t - e_i) - 1, so every
profile is admissible: entries <= D_i, sum n - 1.  Random object: (x0,x1,x2,x3) a uniform ordered 4-tuple of
distinct vertices and an independent uniform colour permutation sigma from the group Gt of permutations
preserving t; P = colours of the six pairs under sigma o c.  The law of P is invariant under S_4 x Gt, so
E[F(P)] = E[Sym F(P)].  (sigma o c is again t-avoiding, with profiles sigma(d), and the admissible set is
Gt-invariant.)

Terms (every constant recomputed here):
  star term  G = sum_s y_s 1[(c01, c02, c03) = s]:  E[G] = (1/n) sum_v J(d(v)),
             J(d) = sum_s y_s d_{s0} (d_{s1} - [s1=s0]) (d_{s2} - [s2=s0] - [s2=s1]) / ((n-1)(n-2)(n-3)).
  'up'  (rho, j, c):  1[roots = rho] (1[c(x_j x3) = c] - (D_c - deg)/(n-3))      E <= 0  (d_c(x_j) <= D_c)
  'low' (rho, j, c):  1[roots = rho] ((Lo_c - deg)/(n-3) - 1[c(x_j x3) = c])     E <= 0,
             Lo_c = n - 1 - sum_{c' != c} D_{c'} <= d_c(x_j);  deg = #{roots l != j : rho(j,l) = c}.
  'int' (rho, J, a):  1[roots = rho] (1[c(x_j x3) = a_j for j in J] - q/(n-3)), q = R(t - w) - 1 - (roots
             outside J lying in S), w_i = largest colour-i clique among {x_j : j in J, a_j = i}.  E <= 0.
  square (colour c, keys, lam, v):  Q = 1[c01 = c] lam ((N-1)/N v[k(x2)] v[k(x3)] + v[k(x2)]^2 / N),
             k(y) = (c(x0 y), c(x1 y)), N = n - 2.  E[Q] = lam E[1[c01=c] (mean_y v[k(y)])^2] >= 0.
F = G + sum z row - sum Q, with z, lam >= 0.  Valid iff  min over valid labelled patterns of Sym F  >
max over admissible profiles of J.  Then E[F] <= E[G] <= max J < min Sym F <= E[F].
"""
import json, sys
from fractions import Fraction as Fr
from itertools import permutations, product, combinations

PAIRS = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

# Ramsey inputs: exact values or published/proved upper bounds (two colours, entries sorted)
# published bounds only (Table 2 of the paper / [Rad26]); the unpublished starred AM bounds R(4,6) <= 40,
# R(4,7) <= 58, R(4,8) <= 79, R(5,6) <= 85 are NOT in the base table and must be given with --input.
R2 = {(3, 3): 6, (3, 4): 9, (3, 5): 14, (3, 6): 18, (3, 7): 23, (3, 8): 28, (3, 9): 36, (3, 10): 41,
      (4, 4): 18, (4, 5): 25, (4, 6): 41, (4, 7): 61, (4, 8): 84, (5, 5): 46, (5, 6): 87}
# three colours (base inputs): literature values R(3,3,3) = 17 [GG55], R(3,3,4) = 30 [CFIM16], R(3,3,5) <= 57 and
# R(3,4,4) <= 77 (recurrence), and hand-proved theorems of the paper: R(3,3,6) <= 88, R(3,3,7) <= 129,
# R(3,4,5) <= 155.  Further (new) inputs are given on the command line with --input and printed.
R3_BASE = {(3, 3, 3): 17, (3, 3, 4): 30, (3, 3, 5): 57, (3, 4, 4): 77, (3, 3, 6): 88, (3, 4, 5): 155,
           (3, 3, 7): 129, (3, 3, 8): 179, (3, 4, 6): 276, (3, 5, 5): 346, (3, 4, 7): 458}
# (3,3,8) <= 179: Theorem 4.x of the paper; (3,4,6) <= 276, (3,5,5) <= 346: Theorems 6.3, 6.4;
# (3,4,7) <= 458: Proposition 6.5 without starred inputs.


def make_ramsey(extra):
    tab = dict(R3_BASE)
    tab2 = dict(R2)
    for k, v in extra.items():
        k = tuple(sorted(k))
        if len(k) == 2:
            assert k in tab2 and v <= tab2[k], 'an input may only lower a bound'
            tab2[k] = v
            continue
        assert len(k) == 3 and k[0] >= 3
        assert v <= tab.get(k, 10 ** 9), 'an input may only lower a bound'
        tab[k] = v

    used = {}

    def ramsey(s):
        s = tuple(sorted(s))
        assert s[0] >= 1
        if s[0] == 1:
            return 1
        if s[0] == 2:
            a, b = s[1], s[2]
            if a == 1:
                return 1
            if a == 2:
                return b
            used[(a, b)] = tab2[(a, b)]
            return tab2[(a, b)]
        used[s] = tab[s]
        return tab[s]
    ramsey.used = used
    return ramsey


def build_terms(cert, extra_inputs=None):
    """Returns (F, J, profs, D, valid, group, extra): F(p) the certificate function on labelled patterns
    p (dict pair -> colour), J(d) the star term at profile d.  The Ramsey inputs are the base inputs plus
    extra_inputs (from the command line); any 'R3' field in the certificate file is ignored."""
    t = tuple(cert['t']); n = int(cert['n'])
    extra = dict(extra_inputs or {})
    ramsey = make_ramsey(extra)
    D = [ramsey([t[k] - (k == i) for k in range(3)]) - 1 for i in range(3)]
    if 'D' in cert:
        assert list(cert['D']) == D, ('degree caps mismatch', cert['D'], D)
    profs = [(a, b, n - 1 - a - b) for a in range(D[0] + 1) for b in range(D[1] + 1) if 0 <= n - 1 - a - b <= D[2]]
    Gt = [s for s in permutations(range(3)) if all(t[s[c]] == t[c] for c in range(3))]
    nf = n - 3; N = n - 2

    def col3(rho, i, j):
        if i > j:
            i, j = j, i
        return {(0, 1): rho[0], (0, 2): rho[1], (1, 2): rho[2]}[(i, j)]

    def max_clique(vs, rho, c):
        for r in range(len(vs), 0, -1):
            for S in combinations(vs, r):
                if all(col3(rho, a, b) == c for a, b in combinations(S, 2)):
                    return r
        return 0

    def cap_q(rho, J, a):
        w = [max_clique([j for j, aj in zip(J, a) if aj == i], rho, i) for i in range(3)]
        s = [t[i] - w[i] for i in range(3)]
        assert min(s) >= 1
        known = sum(1 for l in range(3) if l not in J and all(col3(rho, l, j) == aj for j, aj in zip(J, a)))
        return ramsey(s) - 1 - known

    ys = {tuple(s['star']): Fr(s['mult']) for s in cert['stars']}
    rows = {}
    for r in cert['rows']:
        kind, rho, J, a, z = r['kind'], tuple(r['rho']), tuple(r['J']), tuple(r['a']), Fr(r['mult'])
        assert z >= 0
        if kind == 'int':
            q = cap_q(rho, J, a)
        else:
            (j,), (c,) = J, a
            deg = sum(1 for l in range(3) if l != j and col3(rho, j, l) == c)
            q = D[c] - deg if kind == 'up' else (n - 1 - sum(D) + D[c]) - deg
            assert kind in ('up', 'low')
        assert int(r['q']) == q, ('constant mismatch', r, q)
        rows.setdefault(rho, []).append((kind, J, a, z, Fr(q, nf)))
    sqs = {}
    for s in cert['squares']:
        lam = Fr(s['lam']); assert lam >= 0
        vec = {tuple(k): Fr(v) for k, v in zip(s['keys'], s['vec'])}
        sqs.setdefault(int(s['root_colour']), []).append((lam, vec))

    def F(p):
        v = ys.get((p[(0, 1)], p[(0, 2)], p[(0, 3)]), Fr(0))
        rho = (p[(0, 1)], p[(0, 2)], p[(1, 2)])
        for kind, J, a, z, qq in rows.get(rho, ()):
            ev = 1 if all(p[(j, 3)] == aj for j, aj in zip(J, a)) else 0
            v += z * ((ev - qq) if kind != 'low' else (qq - ev))
        for lam, vec in sqs.get(p[(0, 1)], ()):
            a2 = vec.get((p[(0, 2)], p[(1, 2)]), 0); a3 = vec.get((p[(0, 3)], p[(1, 3)]), 0)
            v -= lam * (Fr(N - 1, N) * a2 * a3 + Fr(1, N) * a2 * a2)
        return v

    def valid(p):
        for c in range(3):
            for S in combinations(range(4), t[c]):
                if all(p[e] == c for e in combinations(S, 2)):
                    return False
        return True

    group = [(pi, s) for pi in permutations(range(4)) for s in Gt]
    den = (n - 1) * (n - 2) * (n - 3)

    def J(d):
        tot = Fr(0)
        for s, y in ys.items():
            dd = list(d); v = 1
            for c in s:
                v *= dd[c]; dd[c] -= 1
            tot += y * v
        return tot / den
    F.used = ramsey.used
    return F, J, profs, D, valid, group, extra


def check(path, extra_inputs=None, verbose=True):
    cert = json.load(open(path))
    t = tuple(cert['t']); n = int(cert['n'])
    F, J, profs, D, valid, group, extra = build_terms(cert, extra_inputs)
    cache = {}
    worst = None; nvalid = 0
    for labs in product(range(3), repeat=6):
        p = dict(zip(PAIRS, labs))
        if not valid(p):
            continue
        nvalid += 1
        tot = Fr(0)
        for pi, s in group:
            g = {}
            for (i, j), c in p.items():
                a, b = pi[i], pi[j]
                g[(min(a, b), max(a, b))] = s[c]
            key = tuple(g[e] for e in PAIRS)
            if key not in cache:
                cache[key] = F(g)
            tot += cache[key]
        val = tot / len(group)
        worst = val if worst is None or val < worst else worst
    Jmax = max(J(d) for d in profs) if profs else None
    ok = (not profs) or worst > Jmax
    if verbose:
        us = sorted(F.used.items(), key=lambda kv: (len(kv[0]), kv[0]))
        print('  Ramsey inputs looked up (caps |S| <= R - 1): ' + ', '.join(
            f'R{k}<={v}{" [input]" if tuple(sorted(k)) in extra else ""}' for k, v in us))
        print(f'{path}: t={t} n={n} D={tuple(D)} inputs=base{(" + " + ", ".join(f"R{k}<={v}" for k, v in extra.items())) if extra else " only"}; {len(profs)} admissible profiles, '
              f'{nvalid} valid labelled patterns; min Sym F - max J = '
              f'{float(worst - Jmax) if profs else "n/a"} -> {"VALID" if ok else "INVALID"}')
    return ok


if __name__ == '__main__':
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('certs', nargs='+')
    ap.add_argument('--input', action='append', default=[], help='extra Ramsey bound, e.g. 3,4,4:75 or 4,7:58')
    args = ap.parse_args()
    extra = {}
    for item in args.input:
        k, v = item.split(':')
        extra[tuple(sorted(int(x) for x in k.split(',')))] = int(v)
    res = [check(p, extra) for p in args.certs]
    print('ALL VALID' if all(res) else 'SOME INVALID')
    sys.exit(0 if all(res) else 1)
