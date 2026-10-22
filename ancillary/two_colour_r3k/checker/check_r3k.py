#!/usr/bin/env python3
"""Independent exact checker for the R(3,k) upper-bound certificates.

Written from the definitions; does not import the generating programs.

Definitions.  A (3,k;n)-graph is a triangle-free graph on n vertices with
independence number < k; e(3,k,n) is its least number of edges (INF if none).
A number m is a *valid lower bound* m_k(n) if every (3,k;n)-graph has >= m
edges; B is a *valid cap* B_k if no (3,k;B)-graph exists, i.e. R(3,k) <= B.

Facts used (each with its proof or citation):
 (F1) In a (3,k;n)-graph G, N(v) is independent, so d_v <= k-1; and
      G_v = G - N[v] is a (3,k-1;n-1-d_v)-graph, so n-1-d_v <= B_{k-1}-1.
 (F2) e(G_v) = e(G) - Z_v with Z_v = sum_{u in N(v)} d_u (N(v) independent),
      and sum_v Z_v = sum_v d_v^2.  Hence (Graver-Yackel, GR13 (4))
        sum_v [d_v^2 + m_{k-1}(n-1-d_v)] <= n e(G),
      i.e. sum_v phi(d_v) <= 0 with phi(h) = h^2 + m_{k-1}(n-1-h) - n h/2.
 (F3) If phi(h) >= alpha - beta h at every admissible degree h, beta > 0,
      then 0 >= n alpha - 2 beta e, so e >= n alpha/(2 beta).
      If phi(h) > 0 at every admissible h, no (3,k;n)-graph exists.
 (F4) Deleting a vertex: e(G) >= m_k(n-1) + min degree >= m_k(n-1) + max(0, n - B_{k-1}).
 (F5) Radziszowski-Kreher (GR13 Theorem 2): formula for e(3,k+1,n) for
      n <= 13k/4 - 1, and e(3,k+1,n) >= 6n - 13k for all n.
 (F6) Cited exact values / lower bounds for k <= 10: GR13 Tables 3, 4, 5,
      parsed here from the text of arXiv:1210.5826v4, and R(3,10) <= 41
      (Angeltveit, arXiv:2401.00392) unless --r310=42.
 (F7) Per-vertex test (only for rows of type 'pv'): every vertex v satisfies
      Z_v <= e - m_{k-1}(n-1-d_v), and Z_v is at least the sum of the d_v
      smallest degrees among the other n-1 vertices.  Orders e for which no
      degree sequence satisfies (F1), (F2) and this test are excluded.
"""
import sys, json, os, re
from fractions import Fraction as Fr
from math import ceil

INF = None
HERE = os.path.dirname(os.path.abspath(__file__))


def ceil_fr(x):
    x = Fr(x)
    return -((-x.numerator) // x.denominator)


# ---------------------------------------------------------------- inputs
def parse_inputs(r310=41):
    base = {k: {} for k in range(3, 11)}
    # Table 3: rows "n v v v ...", right-aligned so the last entry is k = min(n,16)
    for line in open(os.path.join(HERE, 'gr13_table3.txt'), encoding='utf-8'):
        toks = line.split()
        if not toks or not toks[0].isdigit():
            continue
        n = int(toks[0])
        if n < 3 or n > 31 or len(toks) < 2:
            continue
        if not all(t.isdigit() or t == '∞' for t in toks[1:]):
            continue
        vals = toks[1:]
        kmax = min(n, 16)
        for j, t in enumerate(vals):
            k = kmax - (len(vals) - 1 - j)
            v = INF if t == '∞' else int(t)
            if 3 <= k <= 10:
                base[k][n] = v
    for fn, k in (('gr13_table4.txt', 9), ('gr13_table5.txt', 10)):
        for line in open(os.path.join(HERE, fn), encoding='utf-8'):
            toks = line.split()
            if len(toks) >= 2 and toks[0].isdigit():
                n = int(toks[0])
                v = INF if toks[1] == '∞' else int(toks[1])
                base[k][n] = v
    if r310 == 41:
        base[10][41] = INF  # Angeltveit
    tables, caps = {}, {}
    for k in range(3, 11):
        t = {}
        n = 0
        while True:
            if n < k:
                t[n] = 0
            elif n in base[k]:
                t[n] = base[k][n]
            else:
                ex, v = rk(k, n)
                assert ex, ('gap in cited table', k, n)
                t[n] = v
            if t[n] is INF:
                caps[k] = n
                del t[n]
                break
            n += 1
        tables[k] = t
    return tables, caps


def rk(k, n):
    """GR13 Theorem 2 for e(3,k,n), written with K = k-1: returns (exact, value)."""
    K = k - 1
    if n <= K:
        return True, 0
    if n <= 2 * K:
        return True, n - K
    if 2 * n <= 5 * K:
        return True, 3 * n - 5 * K
    if n <= 3 * K:
        return True, 5 * n - 10 * K
    if 4 * n <= 13 * K - 4:
        return True, 6 * n - 13 * K
    return False, 6 * n - 13 * K


# ---------------------------------------------------------------- checks
class Fail(Exception):
    pass


def admissible(k, n, Bprev):
    lo = max(0, n - Bprev)
    hi = min(k - 1, n - 1)
    return [h for h in range(lo, hi + 1) if n - 1 - h <= Bprev - 1]


def phi(h, n, Mprev):
    return Fr(h * h + Mprev[n - 1 - h]) - Fr(n * h, 2)


def line_bound(k, n, h1, h2, Mprev, Bprev):
    A = admissible(k, n, Bprev)
    if not (h1 in A and h2 in A and h1 < h2):
        raise Fail(f'edge ends not admissible {h1},{h2}')
    p1, p2 = phi(h1, n, Mprev), phi(h2, n, Mprev)
    slope = (p2 - p1) / (h2 - h1)
    beta = -slope
    if beta <= 0:
        raise Fail('beta <= 0')
    alpha = p1 + beta * h1
    for h in A:
        if phi(h, n, Mprev) < alpha - beta * h:
            raise Fail(f'line above phi at h={h}')
    return ceil_fr(Fr(n) * alpha / (2 * beta))


def all_positive(k, n, Mprev, Bprev):
    A = admissible(k, n, Bprev)
    return all(phi(h, n, Mprev) > 0 for h in A)


def brute_best_line(k, n, Mprev, Bprev):
    """Best bound from (F3) by brute force over pairs (used only for rare rows)."""
    A = admissible(k, n, Bprev)
    if not A:
        return None
    best = n * A[0] // 2 + (n * A[0]) % 2  # ceil(n*minA/2)
    best = ceil_fr(Fr(n * A[0], 2))
    P = {h: phi(h, n, Mprev) for h in A}
    for i, h1 in enumerate(A):
        for h2 in A[i + 1:]:
            beta = -(P[h2] - P[h1]) / (h2 - h1)
            if beta <= 0:
                continue
            alpha = P[h1] + beta * h1
            if all(P[h] >= alpha - beta * h for h in A):
                best = max(best, ceil_fr(Fr(n) * alpha / (2 * beta)))
    return best


def pv_excluded(k, n, e, Mprev, Bprev):
    """True if no degree sequence for a (3,k;n,e)-graph passes (F1),(F2),(F7).
    Plain recursive enumeration with exact integer pruning."""
    A = admissible(k, n, Bprev)
    if not A:
        return True
    A = sorted(A, reverse=True)
    f = {h: h * h + Mprev[n - 1 - h] for h in A}
    budget = n * e
    fmin_suffix = []
    # minimal f over suffix (valid, weak lower bound on remaining cost per vertex)
    for j in range(len(A)):
        fmin_suffix.append(min(f[h] for h in A[j:]))
    counts = {}
    found = [False]

    def test():
        ms = sorted([h for h in A for _ in range(counts.get(h, 0))])
        for d in A:
            if counts.get(d, 0) == 0:
                continue
            others = list(ms)
            others.remove(d)
            if d > len(others):
                return False
            z = sum(others[:d])
            if z > e - Mprev[n - 1 - d]:
                return False
        return True

    def rec(j, r, s, cost):
        if found[0]:
            return
        if r == 0:
            if s == 0 and cost <= budget and test():
                found[0] = True
            return
        if j == len(A):
            return
        if cost + r * fmin_suffix[j] > budget:
            return
        # degree sum feasibility
        if s > r * A[j] or s < r * A[-1]:
            return
        h = A[j]
        for c in range(min(r, s // h if h else r), -1, -1):
            counts[h] = c
            rec(j + 1, r - c, s - c * h, cost + c * f[h])
            if found[0]:
                break
        counts[h] = 0

    rec(0, n, 2 * e, 0)
    return not found[0]


def verify_row(k, n, m, just, M, Mprev, Bprev, depth=0):
    """Return True if the claimed m is justified."""
    t = just[0]
    if t == 'trivial':
        return n < k and m <= 0
    if t == 'thm2':
        ex, v = rk(k, n)
        return ex and m <= v
    if t == 'thm2lb':
        return m <= 6 * n - 13 * (k - 1)
    if t == 'delete':
        return n - 1 in M and m <= M[n - 1] + max(0, n - Bprev)
    if t == 'left':
        A = admissible(k, n, Bprev)
        return bool(A) and just[1] == A[0] and m <= ceil_fr(Fr(n * A[0], 2))
    if t == 'edge':
        return m <= line_bound(k, n, just[1], just[2], Mprev, Bprev)
    if t == 'pv':
        e0 = just[1]
        if not verify_row(k, n, e0, just[2], M, Mprev, Bprev, depth + 1):
            return False
        for e in range(e0, m):
            if not pv_excluded(k, n, e, Mprev, Bprev):
                raise Fail(f'pv: e={e} not excluded')
        return True
    raise Fail(f'unknown justification {t}')


def verify_cap(k, n, just, M, Mprev, Bprev):
    t = just[0]
    if t == 'empty':
        return not admissible(k, n, Bprev)
    if t == 'infeasible':
        A = admissible(k, n, Bprev)
        return bool(A) and all_positive(k, n, Mprev, Bprev)
    if t == 'edges>max':
        cands = [6 * n - 13 * (k - 1), M[n - 1] + max(0, n - Bprev)]
        b = brute_best_line(k, n, Mprev, Bprev)
        if b is not None:
            cands.append(b)
        return 2 * max(cands) > n * (k - 1)
    if t == 'pv-infeasible':
        e0 = just[1]
        emax = n * (k - 1) // 2
        cands = [6 * n - 13 * (k - 1), M[n - 1] + max(0, n - Bprev)]
        b = brute_best_line(k, n, Mprev, Bprev)
        if b is not None:
            cands.append(b)
        if max(cands) > e0:
            pass
        if e0 > max(cands):
            raise Fail('pv-infeasible start not justified')
        for e in range(e0, emax + 1):
            if not pv_excluded(k, n, e, Mprev, Bprev):
                raise Fail(f'pv-infeasible: e={e} survives')
        return True
    raise Fail(f'unknown cap justification {t}')


def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('cert')
    ap.add_argument('--r310', type=int, default=41)
    ap.add_argument('--override', action='append', default=[],
                    help='k,n,value : override a cited input (negative controls)')
    ap.add_argument('--claim', action='append', default=[],
                    help='k,B : additionally require the certificate to prove R(3,k) <= B')
    args = ap.parse_args()
    tables, caps = parse_inputs(args.r310)
    for o in args.override:
        k, n, v = map(int, o.split(','))
        tables[k][n] = v
    cert = json.load(open(args.cert))
    M = dict(tables)
    B = dict(caps)
    nrows = 0
    nadm = 0
    for ks in sorted(cert['levels'], key=int):
        k = int(ks)
        lev = cert['levels'][ks]
        Bk = lev['B']
        Mprev, Bprev = M[k - 1], B[k - 1]
        Mk = {}
        rows = lev['rows']
        if [r[0] for r in rows] != list(range(0, Bk + 1)):
            raise Fail(f'k={k}: rows must be n=0..B')
        for n, m, just in rows[:-1]:
            if m is None:
                raise Fail(f'k={k} n={n}: missing value below B')
            try:
                ok = verify_row(k, n, m, just, Mk, Mprev, Bprev)
            except Fail as ex:
                print(f'REJECT k={k} n={n} m={m}: {ex}')
                return 1
            if not ok:
                print(f'REJECT k={k} n={n} m={m} just={just}')
                return 1
            Mk[n] = m
            nrows += 1
            nadm += len(admissible(k, n, Bprev))
        n, m, just = rows[-1]
        try:
            ok = verify_cap(k, n, just, Mk, Mprev, Bprev)
        except Fail as ex:
            print(f'REJECT cap k={k} n={n}: {ex}')
            return 1
        if not ok:
            print(f'REJECT cap k={k} n={n} just={just}')
            return 1
        M[k], B[k] = Mk, Bk
        print(f'k={k}: R(3,{k}) <= {Bk} verified', flush=True)
    for c in args.claim:
        k, b = map(int, c.split(','))
        if B.get(k, 10**9) > b:
            print(f'CLAIM FAILED: R(3,{k}) <= {b} not established (have {B.get(k)})')
            return 1
    print(f'ACCEPT: {nrows} rows, {nadm} admissible degrees checked')
    return 0


if __name__ == '__main__':
    sys.exit(main())
