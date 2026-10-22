#!/usr/bin/env python3
"""Exact checker for five-vertex flag certificates proving R(4,4,4) <= n.

Written from the definitions, independently of the search code.  Usage:
    python3 check5.py [--r344=K] CERT.txt [CERT2.txt ...]
(--r344=K: use the hypothesis R(3,4,4) <= K instead of the published R(3,4,4) <= 77; then every colour degree
 is at most K-1.  Default K = 77.)

Setting.  c is a (4,4,4;n)-colouring.  Pick an ordered 5-tuple (x0,...,x4) of distinct vertices uniformly at
random and, independently, a uniform bijection sigma from the colours to the labels 0,1,2; write
c_ij = sigma(c(x_i x_j)).  The law of the labelled colouring (c_ij) of K5 is invariant under S5 x S3, and it
gives probability 0 to every labelled colouring containing a monochromatic K4.

Certificate (plain text, one item per line, see load_text; read into a dict):
  n, star = {'4','31','22','211'} -> Fraction  (coefficients of the four classes of the star x0x1..x0x4
            by colour multiplicities: 4, 3+1, 2+2, 2+1+1),
  caps = list of (kind, p4, kap, q, mu):  p4 = labels of x0x1,x0x2,x0x3,x1x2,x1x3,x2x3;  kap = 4-tuple,
         kap[r] a label or None;  S = intersection over r with kap[r] set of N_{kap[r]}(x_r).
         kind 'up':  ell = 1[p4] (1[x4 in S] - q/(n-4)),  valid (E ell <= 0) if q >= cap(S) - #{x_r in S}.
         kind 'low' (one root r):  ell = 1[p4] (q/(n-4) - 1[x4 in S]),  valid if q <= (n-1-2*76) - #{x_r in S}.
  squares = list of (block, v, lam), lam >= 0; the integrand of a square is >= 0 in expectation:
     'edge'   : E[1[c01=0] (v0 + Z/(n-2))^2],  Z = sum_{w != x0,x1} v[1+3 c(x0w)+c(x1w)]
     'tri'+tau: E[1[(c01,c02,c12)=tau] (v0 + Z/(n-3))^2],  Z = sum_{w not in x0,x1,x2} v[1+9c(x0w)+3c(x1w)+c(x2w)]
                (tau given as a 3-tuple of labels in the field 'tau')
     'vpair'  : E[(v0 + Z/C(n-1,2))^2],  Z = sum over unordered pairs {a,b} of other vertices of
                v[1 + 3*P(min(c0a,c0b),max(c0a,c0b)) + c(ab)],  P = index in [(0,0),(0,1),(0,2),(1,1),(1,2),(2,2)].
     'eloc'   : edge-rooted localising square, field spec = (kind, b, c, q) with b, c labels or None.  On c01 = 0 let
                S = {w not in {x0,x1}: c(x0w) = b if b set, c(x1w) = c if c set} and A = (1/N) sum_w v[1+3c(x0w)+c(x1w)],
                N = n-2.  kind 'up' (valid if q >= cap(S') - #{x0,x1 in S'}, S' the same intersection without excluding
                x0, x1): (q - |S|)(v0 + A)^2 >= 0 pointwise.  kind 'low' (exactly b set, valid if
                q <= n-1-2*76 - [b = 0]): (|S| - q)(v0 + A)^2 >= 0 pointwise.  The integrand over distinct x2,x3,x4 is
                ((q EQ - H)/N resp. (H - q EQ)/N, with u_i = v[1+3c(x0xi)+c(x1xi)], s2 = [x2 in S]:
                EQ = v0^2 + 2 v0 u2 + u2^2/N + (N-1)/N u2 u3                       (expectation = (v0 + A)^2),
                H  = N v0^2 s2 + 2 v0 (s2 u2 + (N-1) s2 u3)
                     + (s2 u2^2 + 2(N-1) s2 u2 u3 + (N-1) s2 u3^2 + (N-1)(N-2) s2 u3 u4)/N   (expectation = |S|(v0 + A)^2).
Then F = sum_cls star[cls] 1[cls] - sum mu ell + sum lam sq.  The checker verifies
  (A) every q from the Ramsey values R(3,4,4) <= 77 (or <= K under --r344=K), R(3,3,4) = 30, R(3,3,3) = 17, R(4,4) = 18, R(3,4) = 9,
      R(3,3) = 6, R(2,k) = k, R(1,...) = 1;  mu >= 0, lam >= 0;
  (B) for every S5 x S3 orbit of labelled colourings of K5 without a monochromatic K4, sum of F over the orbit <= 0;
  (C) J(d) = sum_cls star[cls] P(cls | d) > 0 for every profile d = (d0,d1,d2), 0 <= d_i <= 76, sum n-1,
      where P(cls | d) is the probability that the star at a vertex of profile d has that class.
E[F] >= E[star part] = average over x0 of J(d(x0)) > 0 by (A), but E[F] <= 0 by (B): no (4,4,4;n)-colouring.
"""
import sys
from fractions import Fraction as Fr
from itertools import combinations, product
from math import comb

R344 = 77
DMAX = R344 - 1
EDGES = list(combinations(range(5), 2))
EIX = {e: i for i, e in enumerate(EDGES)}


def c_(p, i, j):
    return p[EIX[(i, j) if i < j else (j, i)]]


def ramsey(s):
    s = tuple(sorted(s))
    if s[0] <= 1: return 1
    if s[0] == 2:
        a, b = s[1], s[2]
        if a == 2: return b
        return {(3, 3): 6, (3, 4): 9, (4, 4): 18}[(a, b)]
    return {(3, 3, 3): 17, (3, 3, 4): 30, (3, 4, 4): R344}[s]


def cap_of(kap, edge):
    """cap on |S|, S = cap_{r: kap[r] set} N_{kap[r]}(x_r); edge(r,r') = label of x_r x_r'."""
    roots = [r for r in range(4) if kap[r] is not None]
    s = []
    for a in range(3):
        A = [r for r in roots if kap[r] == a]
        best = 0
        for k in range(1, len(A) + 1):
            for sub in combinations(A, k):
                if all(edge(u, v) == a for u, v in combinations(sub, 2)): best = max(best, k)
        s.append(4 - best)
    return ramsey(s) - 1


def known_of(kap, edge):
    roots = [r for r in range(4) if kap[r] is not None]
    return sum(1 for r in range(4) if r not in roots and all(edge(r, r2) == kap[r2] for r2 in roots))


def star_class(labels):
    m = sorted([labels.count(a) for a in range(3)], reverse=True)
    return {(4, 0, 0): '4', (3, 1, 0): '31', (2, 2, 0): '22', (2, 1, 1): '211'}[tuple(m)]


def has_mono_k4(p):
    for q in combinations(range(5), 4):
        cols = {c_(p, a, b) for a, b in combinations(q, 2)}
        if len(cols) == 1: return True
    return False


def orbits_union_find(allp, index):
    parent = list(range(len(allp)))
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]; x = parent[x]
        return x
    gens_v = [(1, 0, 2, 3, 4), (1, 2, 3, 4, 0)]
    gens_c = [(1, 0, 2), (1, 2, 0)]
    for i, p in enumerate(allp):
        imgs = []
        for vp in gens_v:
            imgs.append(tuple(c_(p, vp[a], vp[b]) for a, b in EDGES))
        for cp in gens_c:
            imgs.append(tuple(cp[x] for x in p))
        for q in imgs:
            a, b = find(i), find(index[q])
            if a != b: parent[a] = b
    return [find(i) for i in range(len(allp))]


def load_text(path):
    """plain-text certificate (rationals p/q; '-' marks an unset root or colour), one item per line:
      n N
      star CLASS P/Q                                   (classes 4, 31, 22, 211)
      cap KIND p4(6 labels) kap(4 entries, '-' = unset) q MU
      square BLOCK lam v0 ... v_{L-1} [| extra]        extra: tau (3 labels) for 'tri', 'kind b c q' for 'eloc'"""
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
    star = {k: Fr(v) for k, v in d['star'].items()}
    # (A) caps
    caps = []
    for kind, p4, kap, q, mu in d['caps']:
        mu = Fr(mu); q = Fr(q)
        assert mu >= 0, 'negative multiplier'
        if mu == 0: continue
        e4 = {(0, 1): p4[0], (0, 2): p4[1], (0, 3): p4[2], (1, 2): p4[3], (1, 3): p4[4], (2, 3): p4[5]}
        edge = lambda u, v, e4=e4: e4[(min(u, v), max(u, v))]
        kn = known_of(kap, edge)
        if kind == 'up':
            assert q >= cap_of(kap, edge) - kn, ('cap constant too small', kind, p4, kap, q)
        elif kind == 'low':
            assert sum(k is not None for k in kap) == 1
            assert q <= (n - 1 - 2 * DMAX) - kn, ('lower constant too large', p4, kap, q)
        else:
            raise ValueError(kind)
        caps.append((kind, tuple(p4), tuple(kap), q, mu))
    squares = []
    for sq in d['squares']:
        block, v, lam = sq[0], [Fr(x) for x in sq[1]], Fr(sq[2])
        assert lam >= 0
        if lam == 0: continue
        tau = tuple(sq[3]) if len(sq) > 3 else None
        L = {'edge': 10, 'tri': 28, 'vpair': 19, 'eloc': 10}[block]
        if block == 'eloc':
            kind, b, c, q = tau; q = Fr(q)
            assert b is not None or c is not None
            e2 = lambda u, w: 0          # the only root edge is x0x1, label 0
            if kind == 'up':
                kap = (b, c, None, None)
                inS = (1 if (b is None and c == 0) else 0) + (1 if (c is None and b == 0) else 0)
                assert q >= cap_of(kap, e2) - inS, ('eloc cap too small', tau)
            elif kind == 'low':
                assert b is not None and c is None
                assert q <= (n - 1 - 2 * DMAX) - (1 if b == 0 else 0), ('eloc lower constant too large', tau)
            else:
                raise ValueError(kind)
            tau = (kind, b, c, q)
        assert len(v) == L
        squares.append((block, v, lam, tau))
    # (B) orbit sums
    allp = list(product(range(3), repeat=10)); index = {p: i for i, p in enumerate(allp)}
    F = [Fr(0)] * len(allp)
    for i, p in enumerate(allp):
        F[i] += star[star_class([c_(p, 0, j) for j in range(1, 5)])]
    for kind, p4, kap, q, mu in caps:
        for ext in product(range(3), repeat=4):    # labels of x0x4, x1x4, x2x4, x3x4
            p = (p4[0], p4[1], p4[2], ext[0], p4[3], p4[4], ext[1], p4[5], ext[2], ext[3])
            inS = all(kap[r] is None or ext[r] == kap[r] for r in range(4))
            ell = (Fr(int(inS)) - q / n4) if kind == 'up' else (q / n4 - Fr(int(inS)))
            F[index[p]] -= mu * ell
    PAIRS = {(0, 0): 0, (0, 1): 1, (0, 2): 2, (1, 1): 3, (1, 2): 4, (2, 2): 5}
    N2 = comb(n - 1, 2)
    for block, v, lam, tau in squares:
        for i, p in enumerate(allp):
            if block == 'edge':
                if c_(p, 0, 1) != 0: continue
                a2 = v[1 + 3 * c_(p, 0, 2) + c_(p, 1, 2)]; a3 = v[1 + 3 * c_(p, 0, 3) + c_(p, 1, 3)]
                val = v[0] ** 2 + 2 * v[0] * a2 + a2 * a2 / (n - 2) + Fr(n - 3, n - 2) * a2 * a3
            elif block == 'tri':
                if (c_(p, 0, 1), c_(p, 0, 2), c_(p, 1, 2)) != tau: continue
                a3 = v[1 + 9 * c_(p, 0, 3) + 3 * c_(p, 1, 3) + c_(p, 2, 3)]
                a4 = v[1 + 9 * c_(p, 0, 4) + 3 * c_(p, 1, 4) + c_(p, 2, 4)]
                val = v[0] ** 2 + 2 * v[0] * a3 + a3 * a3 / (n - 3) + Fr(n - 4, n - 3) * a3 * a4
            elif block == 'eloc':
                if c_(p, 0, 1) != 0: continue
                kind, b, c, q = tau; N = n - 2
                u2, u3, u4 = (v[1 + 3 * c_(p, 0, i) + c_(p, 1, i)] for i in (2, 3, 4))
                s2 = int((b is None or c_(p, 0, 2) == b) and (c is None or c_(p, 1, 2) == c))
                EQ = v[0] ** 2 + 2 * v[0] * u2 + u2 * u2 / N + Fr(N - 1, N) * u2 * u3
                H = (N * v[0] ** 2 * s2 + 2 * v[0] * (s2 * u2 + (N - 1) * s2 * u3)
                     + (s2 * u2 * u2 + 2 * (N - 1) * s2 * u2 * u3 + (N - 1) * s2 * u3 * u3 + (N - 1) * (N - 2) * s2 * u3 * u4) / Fr(N))
                val = (q * EQ - H) / N if kind == 'up' else (H - q * EQ) / N
            elif block == 'vpair':
                def f(a, b):
                    x, y = c_(p, 0, a), c_(p, 0, b)
                    return v[1 + 3 * PAIRS[(min(x, y), max(x, y))] + c_(p, a, b)]
                f12, f13, f34 = f(1, 2), f(1, 3), f(3, 4)
                val = v[0] ** 2 + 2 * v[0] * f12 + (f12 * f12 + 2 * (n - 3) * f12 * f13 + comb(n - 3, 2) * f12 * f34) / N2
            F[i] += lam * val
    root = orbits_union_find(allp, index)
    sums = {}; sizes = {}; bad = {}
    for i, p in enumerate(allp):
        r = root[i]
        sums[r] = sums.get(r, Fr(0)) + F[i]; sizes[r] = sizes.get(r, 0) + 1
        if r not in bad: bad[r] = has_mono_k4(p)
    worst = max(sums[r] / sizes[r] for r in sums if not bad[r])
    norb = sum(1 for r in sums if not bad[r])
    # (C) profiles
    D4 = (n - 1) * (n - 2) * (n - 3) * (n - 4)
    minJ = None; nprof = 0
    for d0 in range(DMAX + 1):
        for d1 in range(DMAX + 1):
            d2 = n - 1 - d0 - d1
            if not 0 <= d2 <= DMAX: continue
            dd = [d0, d1, d2]; nprof += 1
            J = Fr(0)
            for pat in product(range(3), repeat=4):
                cnt = [0, 0, 0]; num = 1
                for a in pat:
                    num *= dd[a] - cnt[a]; cnt[a] += 1
                J += star[star_class(list(pat))] * Fr(num, D4)
            minJ = J if minJ is None else min(minJ, J)
    ok = worst <= 0 and minJ > 0
    print(f'{label}: n={n}; {len(caps)} caps, {len(squares)} squares; {norb} orbits without mono K4; '
          f'max orbit-average of F = {float(worst):.3e} ({"<= 0 OK" if worst <= 0 else "FAIL"}); '
          f'{nprof} profiles, min J = {float(minJ):.3e} ({"> 0 OK" if minJ > 0 else "FAIL"})')
    return ok


if __name__ == '__main__':
    args = sys.argv[1:]
    for a in [a for a in args if a.startswith('--r344=')]:
        R344 = int(a.split('=')[1]); DMAX = R344 - 1; args.remove(a)
    print(f'hypothesis: R(3,4,4) <= {R344}, colour degrees <= {DMAX}')
    res = [check(p) for p in args]
    print('ALL VALID' if all(res) else 'SOME FAILED')
    sys.exit(0 if all(res) else 1)
