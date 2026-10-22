#!/usr/bin/env python3
"""Exact checker for six-vertex flag certificates proving R(4,4,4) <= n (written from the definitions).

usage: python3 check6.py CERT.txt   (the plain-text format of check5.py; needs numpy)

Setting: a (4,4,4;n)-colouring, a uniform ordered 6-tuple (x0..x5) of distinct vertices and an independent uniform
bijection sigma from colours to labels 0,1,2.  The labelled colouring of K6 has an S6 x S3-invariant law, supported
on colourings without a monochromatic K4.  The certificate has the five-vertex ingredients of check5.py (star
classes of x0x1..x0x4, caps on x0..x3 with free x4, squares 'edge', 'tri', 'vpair', 'eloc' on x0..x4; their
integrands do not involve x5, so their expectations are unchanged), plus six-vertex squares
  'tloc' (spec = (kind, tau, kap, q)): on (c01,c02,c12) = tau, S = {w outside x0,x1,x2 : c(x_r w) = kap[r] for set r},
         A = (1/N) sum_w v[1+9c(x0w)+3c(x1w)+c(x2w)], N = n-3;  'up' (q >= cap(S') - #{x_r in S'}):
         (q - |S|)(v0 + A)^2 >= 0;  'low' (one root r, q <= n-1-2*76 - #{x_r' in S'}): (|S| - q)(v0 + A)^2 >= 0.
         Integrand over distinct x3,x4,x5 (u_i = v[type of x_i], s3 = [x3 in S]): (q EQ - H)/N resp. (H - q EQ)/N with
         EQ = v0^2 + 2 v0 u3 + u3^2/N + (N-1)/N u3 u4,
         H  = N v0^2 s3 + 2 v0 (s3 u3 + (N-1) s3 u4) + (s3 u3^2 + 2(N-1) s3 u3 u4 + (N-1) s3 u4^2 + (N-1)(N-2) s3 u4 u5)/N.
Checks: (A) cap constants and signs, (B) every S6 x S3 orbit average of F <= 0, (C) J > 0 on all profiles.
Exactness: every integrand is a polynomial in the multipliers with coefficients that are rational functions of n;
orbit sums are formed from integer counts (numpy int64 bincounts over the 3^15 labelled colourings) and combined
with Python Fractions.
"""
import sys
from fractions import Fraction as Fr
from itertools import combinations, product
from math import comb
import numpy as np

R344 = 77
DMAX = R344 - 1
E6 = list(combinations(range(6), 2)); EIX = {e: i for i, e in enumerate(E6)}
NP = 3 ** 15
POW = (3 ** np.arange(14, -1, -1)).astype(np.int64)


def ramsey(s):
    s = tuple(sorted(s))
    if s[0] <= 1: return 1
    if s[0] == 2:
        a, b = s[1], s[2]
        if a == 2: return b
        return {(3, 3): 6, (3, 4): 9, (4, 4): 18}[(a, b)]
    return {(3, 3, 3): 17, (3, 3, 4): 30, (3, 4, 4): R344}[s]


def cap_of(kap, edge):
    roots = [r for r in range(len(kap)) if kap[r] is not None]
    s = []
    for a in range(3):
        A = [r for r in roots if kap[r] == a]; best = 0
        for k in range(1, len(A) + 1):
            for sub in combinations(A, k):
                if all(edge(u, v) == a for u, v in combinations(sub, 2)): best = max(best, k)
        s.append(4 - best)
    return ramsey(s) - 1


def known_of(kap, edge, verts):
    roots = [r for r in range(len(kap)) if kap[r] is not None]
    return sum(1 for r in verts if r not in roots and all(edge(r, r2) == kap[r2] for r2 in roots))


# ---------------- colourings and orbits ----------------
def digits():
    codes = np.arange(NP, dtype=np.int64)
    P = np.empty((NP, 15), dtype=np.int8)
    for k in range(15): P[:, k] = (codes // POW[k]) % 3
    return P


def orbits(P):
    def img(vp=None, cp=None):
        out = np.zeros(NP, np.int64)
        for k, (i, j) in enumerate(E6):
            src = k if vp is None else EIX[tuple(sorted((vp[i], vp[j])))]
            col = P[:, src].astype(np.int64)
            if cp is not None: col = np.array(cp, np.int64)[col]
            out += col * POW[k]
        return out.astype(np.int32)
    gens = [img(vp=(1, 0, 2, 3, 4, 5)), img(vp=(1, 2, 3, 4, 5, 0)), img(cp=(1, 0, 2)), img(cp=(1, 2, 0))]
    lab = np.arange(NP, dtype=np.int32)
    while True:
        old = lab
        for g in gens: lab = np.minimum(lab, lab[g])
        lab = lab[lab]
        if np.array_equal(lab, old): break
    valid = np.ones(NP, bool)
    for q in combinations(range(6), 4):
        c = P[:, [EIX[e] for e in combinations(q, 2)]]
        valid &= ~(c == c[:, :1]).all(1)
    _, oid = np.unique(lab, return_inverse=True)
    oid = oid.astype(np.int64)
    noid = oid.max() + 1
    bad = np.zeros(noid, bool); bad[oid[~valid]] = True          # validity is orbit-invariant
    size = np.bincount(oid, minlength=noid)
    return oid, size, ~bad


class Acc:
    """F summed over each orbit, exactly: sum over terms of (rational coefficient) x (integer count)."""
    def __init__(self, oid, nor):
        self.oid = oid; self.nor = nor; self.F = [Fr(0)] * nor
    def add_count(self, coef, mask):
        """F += coef * #{p in orbit: mask(p)}"""
        if coef == 0: return
        cnt = np.bincount(self.oid[mask], minlength=self.nor)
        for o in np.nonzero(cnt)[0]: self.F[o] += coef * int(cnt[o])
    def add_quad(self, coef, mask, i_idx, j_idx, L, s):
        """F += coef * sum_{p in orbit, mask} L[i(p)][j(p)]  (L an s x s list of Fractions)"""
        key = self.oid[mask] * (s * s) + i_idx[mask].astype(np.int64) * s + j_idx[mask]
        u, cnt = np.unique(key, return_counts=True)
        for k, c in zip(u.tolist(), cnt.tolist()):
            o, r = divmod(k, s * s); a, b = divmod(r, s)
            if L[a][b]: self.F[o] += coef * c * L[a][b]


def load_text(path):
    """plain-text certificate, the format of check5.py (rationals p/q; '-' marks an unset root or colour):
      n N
      star CLASS P/Q                                   (classes 4, 31, 22, 211)
      cap KIND p4(6 labels) kap(4 entries, '-' = unset) q MU
      square BLOCK lam v0 ... v_{L-1} [| extra]        extra: tau (3 labels) for 'tri', 'kind b c q' for 'eloc'
    Only the five-vertex blocks have a text form; a 'tloc' square is rejected here."""
    d = dict(star={}, caps=[], squares=[])
    opt = lambda t: None if t == '-' else int(t)
    for line in open(path):
        w = line.split()
        if not w: continue
        if w[0] == 'n': d['n'] = int(w[1])
        elif w[0] == 'star': d['star'][w[1]] = Fr(w[2])
        elif w[0] == 'cap':
            d['caps'].append((w[1], tuple(int(ch) for ch in w[2]), tuple(opt(ch) for ch in w[3]), Fr(w[4]), Fr(w[5])))
        elif w[0] == 'square':
            body, _, extra = line.partition('|'); b = body.split()
            if b[1] not in ('edge', 'tri', 'vpair', 'eloc'): raise ValueError('no text form for block ' + b[1])
            sq = (b[1], [Fr(x) for x in b[3:]], Fr(b[2]))
            if b[1] == 'tri': sq = sq + (tuple(int(ch) for ch in extra.strip()),)
            if b[1] == 'eloc':
                e = extra.split(); sq = sq + ((e[0], opt(e[1]), opt(e[2]), Fr(e[3])),)
            d['squares'].append(sq)
        else: raise ValueError(line)
    return d


def check(path, label=None):
    """path: a plain-text certificate file, or an already loaded certificate dict (used by the controls)."""
    d = path if isinstance(path, dict) else load_text(path)
    if label is None: label = path if isinstance(path, str) else 'certificate'
    n = d['n']; n4 = n - 4
    P = digits(); oid, size, good = orbits(P)
    nor = len(size)
    ec = lambda i, j: P[:, EIX[(i, j) if i < j else (j, i)]]
    acc = Acc(oid, nor)
    ones = np.ones(NP, bool)
    # star classes at x0 over x1..x4
    S4 = np.stack([ec(0, j) for j in range(1, 5)], 1)
    cnt = np.sort(np.stack([(S4 == a).sum(1) for a in range(3)], 1), axis=1)[:, ::-1]
    for cls, pat in [('4', (4, 0, 0)), ('31', (3, 1, 0)), ('22', (2, 2, 0)), ('211', (2, 1, 1))]:
        acc.add_count(Fr(d['star'][cls]), (cnt == np.array(pat)).all(1))
    # caps on x0..x3, free x4
    ncaps = 0
    for kind, p4, kap, q, mu in d['caps']:
        mu = Fr(mu); q = Fr(q)
        assert mu >= 0
        if mu == 0: continue
        e4 = {(0, 1): p4[0], (0, 2): p4[1], (0, 3): p4[2], (1, 2): p4[3], (1, 3): p4[4], (2, 3): p4[5]}
        edge = lambda u, v, e4=e4: e4[(min(u, v), max(u, v))]
        kn = known_of(kap, edge, range(4))
        if kind == 'up': assert q >= cap_of(kap, edge) - kn, ('cap', p4, kap, q)
        elif kind == 'low':
            assert sum(k is not None for k in kap) == 1 and q <= (n - 1 - 2 * DMAX) - kn, ('low', p4, kap, q)
        else: raise ValueError(kind)
        m = ones.copy()
        for (a, b), lab in e4.items(): m &= (ec(a, b) == lab)
        inS = m.copy()
        for r in range(4):
            if kap[r] is not None: inS &= (ec(r, 4) == kap[r])
        sgn = 1 if kind == 'up' else -1                  # up: ell = 1[p4](1[x4 in S] - q/n4); low: negated
        acc.add_count(-mu * sgn, inS); acc.add_count(mu * sgn * q / n4, m)
        ncaps += 1
    # squares: group by (block, spec) and aggregate Lambda = sum lam v v^T exactly
    groups = {}
    for sq in d['squares']:
        block, v, lam = sq[0], [Fr(x) for x in sq[1]], Fr(sq[2])
        assert lam >= 0
        if lam == 0: continue
        spec = tuple(sq[3]) if len(sq) > 3 else None
        L = {'edge': 10, 'tri': 28, 'vpair': 19, 'eloc': 10, 'tloc': 28}[block]
        assert len(v) == L
        g = groups.setdefault((block, spec), [Fr(0)] * (L * L))
        for a in range(L):
            if v[a] == 0: continue
            la = lam * v[a]
            for b in range(L): g[a * L + b] += la * v[b]
    z = np.zeros(NP, np.int64)
    for (block, spec), flat in groups.items():
        s = {'edge': 10, 'tri': 28, 'vpair': 19, 'eloc': 10, 'tloc': 28}[block]
        L = [flat[a * s:(a + 1) * s] for a in range(s)]
        if block == 'edge':
            m = ec(0, 1) == 0
            k2 = 1 + 3 * ec(0, 2).astype(np.int64) + ec(1, 2); k3 = 1 + 3 * ec(0, 3).astype(np.int64) + ec(1, 3)
            terms = [(1, z, z), (2, z, k2), (Fr(1, n - 2), k2, k2), (Fr(n - 3, n - 2), k2, k3)]
            for c, i, j in terms: acc.add_quad(c, m, i, j, L, s)
        elif block == 'tri':
            tau = spec
            m = (ec(0, 1) == tau[0]) & (ec(0, 2) == tau[1]) & (ec(1, 2) == tau[2])
            a3 = 1 + 9 * ec(0, 3).astype(np.int64) + 3 * ec(1, 3) + ec(2, 3)
            a4 = 1 + 9 * ec(0, 4).astype(np.int64) + 3 * ec(1, 4) + ec(2, 4)
            for c, i, j in [(1, z, z), (2, z, a3), (Fr(1, n - 3), a3, a3), (Fr(n - 4, n - 3), a3, a4)]:
                acc.add_quad(c, m, i, j, L, s)
        elif block == 'vpair':
            PAIRS = {(0, 0): 0, (0, 1): 1, (0, 2): 2, (1, 1): 3, (1, 2): 4, (2, 2): 5}
            def f(a, b):
                x, y = ec(0, a).astype(np.int64), ec(0, b).astype(np.int64)
                lo, hi = np.minimum(x, y), np.maximum(x, y)
                pi = np.zeros(NP, np.int64)
                for (u, w), k in PAIRS.items(): pi[(lo == u) & (hi == w)] = k
                return 1 + 3 * pi + ec(a, b)
            f12, f13, f34 = f(1, 2), f(1, 3), f(3, 4); N2 = comb(n - 1, 2)
            for c, i, j in [(1, z, z), (2, z, f12), (Fr(1, N2), f12, f12), (Fr(2 * (n - 3), N2), f12, f13),
                            (Fr(comb(n - 3, 2), N2), f12, f34)]:
                acc.add_quad(c, ones, i, j, L, s)
        elif block in ('eloc', 'tloc'):
            if block == 'eloc':
                kind, b, cc, q = spec; q = Fr(q); kap = (b, cc); roots = 2; N = n - 2
                edge = lambda u, w: 0
                m = ec(0, 1) == 0
                free = (2, 3, 4)
                typ = {i: 1 + 3 * ec(0, i).astype(np.int64) + ec(1, i) for i in free}
            else:
                kind, tau, kap, q = spec; q = Fr(q); roots = 3; N = n - 3
                e3 = {(0, 1): tau[0], (0, 2): tau[1], (1, 2): tau[2]}
                edge = lambda u, w, e3=e3: e3[(min(u, w), max(u, w))]
                m = (ec(0, 1) == tau[0]) & (ec(0, 2) == tau[1]) & (ec(1, 2) == tau[2])
                free = (3, 4, 5)
                typ = {i: 1 + 9 * ec(0, i).astype(np.int64) + 3 * ec(1, i) + ec(2, i) for i in free}
            assert any(k is not None for k in kap)
            kn = known_of(kap, edge, range(roots))
            if kind == 'up': assert q >= cap_of(kap, edge) - kn, (block, spec)
            elif kind == 'low':
                assert sum(k is not None for k in kap) == 1 and q <= (n - 1 - 2 * DMAX) - kn, (block, spec)
            else: raise ValueError(kind)
            f1, f2, f3 = free
            sm = m.copy()
            for r in range(roots):
                if kap[r] is not None: sm &= (ec(r, f1) == kap[r])
            u1, u2, u3 = typ[f1], typ[f2], typ[f3]
            sg = 1 if kind == 'up' else -1
            # +sg q EQ / N  on m ;  -sg H / N  on sm (s = 1 there)
            EQ = [(1, z, z), (2, z, u1), (Fr(1, N), u1, u1), (Fr(N - 1, N), u1, u2)]
            H = [(N, z, z), (2, z, u1), (2 * (N - 1), z, u2), (Fr(1, N), u1, u1), (Fr(2 * (N - 1), N), u1, u2),
                 (Fr(N - 1, N), u2, u2), (Fr((N - 1) * (N - 2), N), u2, u3)]
            for c, i, j in EQ: acc.add_quad(sg * q * c / N, m, i, j, L, s)
            for c, i, j in H: acc.add_quad(-sg * Fr(c) / N, sm, i, j, L, s)
        else:
            raise ValueError(block)
    worst = max(acc.F[o] / int(size[o]) for o in range(nor) if good[o])
    # (C) profiles
    D4 = (n - 1) * (n - 2) * (n - 3) * (n - 4)
    star = {k: Fr(v) for k, v in d['star'].items()}
    def cls_of(pat):
        mm = tuple(sorted([pat.count(a) for a in range(3)], reverse=True))
        return {(4, 0, 0): '4', (3, 1, 0): '31', (2, 2, 0): '22', (2, 1, 1): '211'}[mm]
    minJ = None; nprof = 0
    for d0 in range(DMAX + 1):
        for d1 in range(DMAX + 1):
            d2 = n - 1 - d0 - d1
            if not 0 <= d2 <= DMAX: continue
            dd = [d0, d1, d2]; nprof += 1; J = Fr(0)
            for pat in product(range(3), repeat=4):
                c = [0, 0, 0]; num = 1
                for a in pat: num *= dd[a] - c[a]; c[a] += 1
                J += star[cls_of(list(pat))] * Fr(num, D4)
            minJ = J if minJ is None else min(minJ, J)
    ok = worst <= 0 and minJ > 0
    print(f'{label}: n={n}; {ncaps} caps, {len(d["squares"])} squares in {len(groups)} groups; {int(good.sum())} orbits '
          f'without mono K4; max orbit-average of F = {float(worst):.3e} ({"<= 0 OK" if worst <= 0 else "FAIL"}); '
          f'{nprof} profiles, min J = {float(minJ):.3e} ({"> 0 OK" if minJ > 0 else "FAIL"})', flush=True)
    return ok


if __name__ == '__main__':
    res = [check(p) for p in sys.argv[1:]]
    print('ALL VALID' if all(res) else 'SOME FAILED')
    sys.exit(0 if all(res) else 1)
