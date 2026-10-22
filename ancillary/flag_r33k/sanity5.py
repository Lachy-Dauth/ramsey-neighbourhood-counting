#!/usr/bin/env python3
"""Soundness test of the five-vertex checker's formulas (check_r33k5.py) on a real (3,3,k;n)-colouring.

From the paper's (3,3,9;132)-colouring (../circulants.json) take iterated green neighbourhoods down to level k
(default: 3 steps, a (3,3,6;26)-colouring).  Compute the exact law of the labelled K5 colouring (ordered 5-tuple, random R/B swap) and check:
  * the 4-star identity E[1[s]] = E_v[P(s | d(v))] for all 81 patterns;
  * each square type: E[q(K)] equals the direct average of the square, for random integer coefficient vectors;
  * every 'up' and 'low' row (all valid pi, all X, a, with the checker's constants) and every floor and the rec
    row with the trivial m: E[g] <= E_v[beta(d(v))].
Usage: python3 sanity5.py [steps] [matrix file]   (default: the n = 132 witness of ../circulants.json)
Standard library only.
"""
import sys, os, json, random, itertools
from collections import Counter
from fractions import Fraction as Fr
import check_r33k as C
import check_r33k5 as F

def load(path):
    """a colour matrix file (rows of 0/1/2); the diagonal is set to -1"""
    A = [[int(c) for c in l.strip()] for l in open(path) if l.strip()]
    for i in range(len(A)): A[i][i] = -1
    return A

def circulant(n):
    """the witness of ../circulants.json with n vertices: 0 red, 1 blue, 2 green, -1 on the diagonal"""
    w = next(w for w in json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'circulants.json')))['witnesses'] if w['n'] == n)
    A, B = set(w['A']), set(w['B'])
    dist = lambda i, j: min((i - j) % n, (j - i) % n)
    return [[-1 if i == j else 0 if dist(i, j) in A else 1 if dist(i, j) in B else 2 for j in range(n)] for i in range(n)]

def law5(A):
    n = len(A); cnt = Counter()
    P = [3 ** (9 - i) for i in range(10)]
    idx = {e: i for i, e in enumerate(F.E5)}
    p01, p02, p12 = P[idx[(0, 1)]], P[idx[(0, 2)]], P[idx[(1, 2)]]
    p03, p13, p23 = P[idx[(0, 3)]], P[idx[(1, 3)]], P[idx[(2, 3)]]
    p04, p14, p24, p34 = P[idx[(0, 4)]], P[idx[(1, 4)]], P[idx[(2, 4)]], P[idx[(3, 4)]]
    for x0, x1, x2 in itertools.permutations(range(n), 3):
        base = A[x0][x1] * p01 + A[x0][x2] * p02 + A[x1][x2] * p12
        r0, r1, r2 = A[x0], A[x1], A[x2]
        rest = [y for y in range(n) if y != x0 and y != x1 and y != x2]
        f4 = {y: r0[y] * p04 + r1[y] * p14 + r2[y] * p24 for y in rest}
        for y3 in rest:
            b3 = base + r0[y3] * p03 + r1[y3] * p13 + r2[y3] * p23; r3 = A[y3]
            for y4 in rest:
                if y4 != y3: cnt[b3 + f4[y4] + r3[y4] * p34] += 1
    out = {}
    for code in cnt:
        K = []; x = int(code)
        for _ in range(10): K.append(x % 3); x //= 3
        K = tuple(reversed(K)); Ks = tuple((1 - v) if v < 2 else v for v in K)
        out[K] = out.get(K, 0) + int(cnt[code]); out[Ks] = out.get(Ks, 0) + int(cnt[code])
    return out

def main(steps, wpath):
    A = load(wpath) if wpath else circulant(132); S = list(range(len(A))); k = 9
    for _ in range(steps):
        v = S[0]; S = [u for u in S if u != v and A[v][u] == 2]; k -= 1
    sub = [[A[i][j] for j in S] for i in S]; n = len(S)
    print(f'real (3,3,{k};{n})-colouring', flush=True)
    law = law5(sub); tot = sum(law.values()); assert tot == 2 * n * (n - 1) * (n - 2) * (n - 3) * (n - 4)
    assert all(F.valid(K) for K in law)
    degs = [tuple(sum(1 for x in sub[v] if x == c) for c in range(3)) for v in range(n)]
    ctx = C.Context(k, n)
    ff4 = (n - 1) * (n - 2) * (n - 3) * (n - 4)
    def E(f): return sum(Fr(m) * f(K) for K, m in law.items()) / tot
    ok = True
    # stars
    bad = 0
    for s in itertools.product(range(3), repeat=4):
        lhs = E(lambda K: 1 if (F.col(K, 0, 1), F.col(K, 0, 2), F.col(K, 0, 3), F.col(K, 0, 4)) == s else 0)
        def ff(dd):
            dd = list(dd); v = 1
            for c in s: v *= dd[c]; dd[c] -= 1
            return v
        rhs = sum(Fr(ff(d) + ff((d[1], d[0], d[2])), 2 * ff4) for d in degs) / n
        bad += lhs != rhs
    print(f'  star identity: {81 - bad}/81 exact'); ok &= bad == 0
    # squares
    rng = random.Random(1)
    def lab(c, sw): return (1 - c) if (sw and c < 2) else c
    bad = 0; tried = 0
    for trial in range(4):
        for typ in ('edge', 'triangle', 'vertex'):
            a0 = rng.randint(-3, 3)
            if typ == 'edge':
                data = rng.choice([0, 2]); keys = list(itertools.product(range(3), repeat=2))
            elif typ == 'triangle':
                data = rng.choice([(2, 2, 2), (0, 2, 2), (0, 0, 2), (0, 1, 2), (0, 0, 1)]); keys = list(itertools.product(range(3), repeat=3))
            else:
                data = None; keys = list(itertools.product(range(3), repeat=3))
            a = {kk: Fr(rng.randint(-4, 4)) for kk in keys}
            s = (Fr(1), typ, data, Fr(a0), a)
            lhs = E(lambda K: F.sq(s, K, n))
            tot_d = Fr(0); cntd = 0
            for sw in (0, 1):
                c = lambda i, j: lab(sub[i][j], sw)
                if typ == 'edge':
                    for x0, x1 in itertools.permutations(range(n), 2):
                        cntd += 1
                        if c(x0, x1) != data: continue
                        Z = sum(a[(c(x0, w), c(x1, w))] for w in range(n) if w not in (x0, x1))
                        tot_d += (a0 + Z / (n - 2)) ** 2
                elif typ == 'triangle':
                    for x0, x1, x2 in itertools.permutations(range(n), 3):
                        cntd += 1
                        if (c(x0, x1), c(x0, x2), c(x1, x2)) != data: continue
                        Z = sum(a[(c(x0, w), c(x1, w), c(x2, w))] for w in range(n) if w not in (x0, x1, x2))
                        tot_d += (a0 + Z / (n - 3)) ** 2
                else:
                    for x0 in range(n):
                        cntd += 1
                        Z = sum(a[(c(x0, w), c(x0, w2), c(w, w2))] for w, w2 in itertools.permutations([u for u in range(n) if u != x0], 2))
                        tot_d += (a0 + Z / ((n - 1) * (n - 2))) ** 2
            rhs = tot_d / cntd; tried += 1; bad += lhs != rhs
    print(f'  square expansions: {tried - bad}/{tried} exact (edge, triangle, vertex types)'); ok &= bad == 0
    # rows
    bypi = {}
    for K, m in law.items(): bypi.setdefault(tuple(K[F.EI[e]] for e in F.E4), []).append((K, m))
    viol = 0; nrows = 0
    for pi, lst in bypi.items():
        base = sum(m for K, m in lst)
        for size in (1, 2, 3, 4):
            for X in itertools.combinations(range(4), size):
                for a in itertools.product(range(3), repeat=size):
                    evc = sum(m for K, m in lst if all(F.col(K, x, 4) == ax for x, ax in zip(X, a)))
                    kinds = ('up', 'low') if size == 1 else ('up',)
                    for kind in kinds:
                        q = F.row_q(kind, pi, X, a, k, ctx.dmin)
                        # E[g] * tot, using the checker's g_up on one representative per event value
                        val = (evc - Fr(q, n - 4) * base) if kind == 'up' else (Fr(q, n - 4) * base - evc)
                        # cross-check g_up itself on the members
                        Kev = next((K for K, m in lst if all(F.col(K, x, 4) == ax for x, ax in zip(X, a))), None)
                        if Kev is not None: assert F.g_up(kind, X, a, q, n, Kev) == ((1 - Fr(q, n - 4)) if kind == 'up' else (Fr(q, n - 4) - 1))
                        nrows += 1; viol += val > 0
    for i in range(3):
        for j in range(3):
            if i < 2 and i == j: continue
            for kind in ('floor_up', 'floor_low'):
                row = (kind, i, j)
                lhs = E(lambda K: F.g3(row, K)); rhs = sum(ctx.beta(row, d) for d in degs) / n
                nrows += 1; viol += lhs > rhs
    mt = {g: C.ceil_half(g * max(0, g - 1 - ctx.C[2][2])) for g in range(n)}
    row = ('rec', mt); lhs = E(lambda K: F.g3(row, K)); rhs = sum(ctx.beta(row, d) for d in degs) / n
    nrows += 1; viol += lhs > rhs
    print(f'  rows: {nrows - viol}/{nrows} satisfy E[g] <= E_v[beta]'); ok &= viol == 0
    print('SANITY5 PASSED' if ok else 'SANITY5 FAILED')
    return ok

if __name__ == '__main__':
    steps = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    w = sys.argv[2] if len(sys.argv) > 2 else None
    sys.exit(0 if main(steps, w) else 1)
