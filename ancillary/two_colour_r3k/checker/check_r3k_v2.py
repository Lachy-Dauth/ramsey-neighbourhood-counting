#!/usr/bin/env python3
"""Exact checker (version 2) for R(3,k) upper-bound certificates written by
make_cert3.py.  It does not import the generating programs (boot2, boot3,
enum3, translp); it imports only check_r3k (the version-1 checker, for the
GR13 input parser and the basic row types) and reads cited inputs from
checker/cited_extra.txt.

Definitions as in check_r3k.py: a (3,k;n,e)-graph is triangle-free with
n vertices, e edges and independence number < k; m_k(n) denotes a verified
lower bound on e(3,k,n) and B_k a verified cap (no (3,k;B_k)-graph).

New row types (in addition to those of check_r3k.py):
 ['back3']      m <= Backelin's lower bound for e(3,k;n) (cited_extra.txt).
 ['seq', e0, inner, maxdeg, excl]
     inner justifies e0; every order e with e0 <= e < m is excluded:
     the checker enumerates ALL degree sequences (c_d) with
        sum c_d = n, sum d c_d = 2e, d admissible (F1), d <= e - m_k(n-1)
        if maxdeg (G - v is a (3,k;n-1)-graph with e - d_v edges),
        sum c_d (d^2 + m_{k-1}(n-1-d)) <= n e                      (F2)
     and requires for each of them an exclusion certificate in excl[e]:
       ['cut']   some vertex class fails the neighbour-count test (T1);
       ['lp', [[name, y], ...]]  Farkas multipliers for the named valid
                 linear constraints (L1)-(L6) below, verified exactly.
 ['seq-infeasible', e0, inner, maxdeg, excl]  (at n = B_k) the same for all
     e0 <= e <= floor(n(k-1)/2).
 ['survey']     (at n = B_k) cited cap R(3,k) <= B_k (cited_extra.txt).

Valid constraints for a (3,k;n,e)-graph G with given degree sequence.
Classes are the distinct degrees a with c_a > 0.  Variables: x_{ab} (a <= b)
= number of edges between class a and class b (x_{aa}: edges inside class a,
present only if c_a >= 2).  Write x_{a->b} = x_{ab} for a != b and
x_{a->a} = 2 x_{aa} (edge ends).  zmax(a) = e - m_{k-1}(n-1-a).
 (L1 'deg' a)  sum_b x_{a->b} = a c_a.
 (L2 'Z' a)    sum_b b x_{a->b} <= c_a zmax(a): the left side is the sum of
               Z_v = sum_{u in N(v)} d_u over v in class a, and
               e(G_v) = e - Z_v >= m_{k-1}(n-1-a) since G_v = G - N[v] is a
               (3,k-1;n-1-a)-graph (N(v) is independent).
 (L3 'Zlo' a)  sum_b b x_{a->b} >= c_a (e - floor((n-1-a)(k-2)/2)): every
               vertex u of G_v has N_{G_v}(u) + v independent in G, so
               deg_{G_v}(u) <= k-2 and e(G_v) <= (n-1-a)(k-2)/2.
 (L4 'Man' S)  sum_{a<=b in S} x_{ab} <= floor(N_S^2/4), N_S = sum_{a in S} c_a
               (Mantel: the subgraph induced by the classes in S is
               triangle-free).
 (L5 'cap' a b) x_{ab} <= c_a c_b (a < b).
 (L6 'cut' a b) sum_{a' <= b} x_{a->a'} >= c_a cmin(a,b), where cmin(a,b) is
               the least integer t, 0 <= t <= a, such that some vertex v of
               degree a with exactly t neighbours of degree <= b can have
               Z_v <= zmax(a): with P the multiset of degrees <= b of the
               vertices other than v and q the least degree > b present,
               Z_v >= (sum of the t smallest of P) + (a - t) q, so t must
               satisfy that this is <= zmax(a) (t <= |P|; if no degree > b is
               present then t = a).  If no t qualifies the sequence is
               impossible (test T1, row 'cut').
A Farkas certificate y (y >= 0 on '>=' rows, y <= 0 on '<=' rows, free on
'=' rows) with sum_r y_r a_r <= 0 in every variable and sum_r y_r b_r > 0
proves the system has no solution x >= 0, so the sequence is impossible.
"""
import sys, os, json
from fractions import Fraction as Fr
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check_r3k as C1

Fail = C1.Fail


def read_cited():
    back3, survey = {}, {}
    for line in open(os.path.join(HERE, 'cited_extra.txt')):
        t = line.split()
        if not t or t[0].startswith('#'):
            continue
        if t[0] == 'back3':
            back3.setdefault(int(t[1]), {})[int(t[2])] = int(t[3])
        elif t[0] == 'survey':
            survey[int(t[1])] = int(t[2])
    return back3, survey


# ------------------------------------------------------------ enumeration
def adm(k, n, Bprev, Mprev, dmax):
    lo = max(0, n - Bprev)
    hi = min(k - 1, n - 1)
    if dmax is not None:
        hi = min(hi, dmax)
    return [h for h in range(lo, hi + 1) if n - 1 - h <= Bprev - 1 and (n - 1 - h) in Mprev]


def lower_hull_int(pts):
    pts = sorted(pts)
    h = []
    for p in pts:
        while len(h) >= 2:
            (x1, y1), (x2, y2) = h[-2], h[-1]
            if (y2 - y1) * (p[0] - x1) >= (p[1] - y1) * (x2 - x1):
                h.pop()
            else:
                break
        h.append(p)
    return h


def all_sequences(k, n, e, Mprev, Bprev, dmax, limit=10**7):
    """All degree sequences satisfying (F1), (F2), degree sum 2e and the
    optional maximum degree.  Exact integer pruning by the lower convex hull
    of f over the degrees still available."""
    A = sorted(adm(k, n, Bprev, Mprev, dmax), reverse=True)
    if not A:
        return []
    f = {h: h * h + Mprev[n - 1 - h] for h in A}
    budget = n * e
    hulls = [lower_hull_int([(h, f[h]) for h in A[j:]]) for j in range(len(A))]

    def prune(j, r, s, cost):
        # True if no completion with r vertices, degree sum s from A[j:] fits
        if r == 0:
            return s != 0 or cost > budget
        h = hulls[j]
        if s < r * h[0][0] or s > r * h[-1][0]:
            return True
        if len(h) == 1:
            return cost + r * h[0][1] > budget
        for (x1, y1), (x2, y2) in zip(h, h[1:]):
            if r * x1 <= s <= r * x2:
                # r*hull(s/r) = r*y1 + (y2-y1)(s - r x1)/(x2-x1)
                return (cost + r * y1 - budget) * (x2 - x1) + (y2 - y1) * (s - r * x1) > 0
        return True

    out = []
    cnt = {}
    nodes = [0]

    def rec(j, r, s, cost):
        nodes[0] += 1
        if nodes[0] > limit:
            raise Fail('enumeration limit')
        if r == 0:
            if s == 0 and cost <= budget:
                out.append({h: c for h, c in cnt.items() if c})
            return
        if j == len(A) or prune(j, r, s, cost):
            return
        h = A[j]
        top = min(r, s // h) if h > 0 else r
        for c in range(top, -1, -1):
            cnt[h] = c
            rec(j + 1, r - c, s - c * h, cost + c * f[h])
        cnt[h] = 0

    rec(0, n, 2 * e, 0)
    return out


# ------------------------------------------------------------ per-sequence tests
def cmin(k, n, e, seq, Mprev, a, b):
    """Least t (0..a) as in (L6), or None if none qualifies."""
    zmax = e - Mprev[n - 1 - a]
    P = []
    for d, c in seq.items():
        if d <= b:
            P.extend([d] * c)
    if a <= b:
        P.remove(a)
    P.sort()
    higher = [d for d in seq if d > b]
    q = min(higher) if higher else None
    for t in range(0, a + 1):
        if t > len(P):
            break
        if q is None and t < a:
            continue
        z = sum(P[:t]) + (a - t) * (q if q is not None else 0)
        if z <= zmax:
            return t
    return None


def cut_fails(k, n, e, seq, Mprev):
    for a in seq:
        for b in seq:
            if cmin(k, n, e, seq, Mprev, a, b) is None:
                return True
    return False


def constraint(k, n, e, seq, Mprev, name):
    """Return (coef dict over (a,b) with a<=b, sense, rhs) for a named
    constraint, computed from the definitions in the module docstring."""
    cls = sorted(seq)
    c = seq

    def var(a, b):
        a, b = min(a, b), max(a, b)
        if a == b and c[a] < 2:
            return None
        return (a, b)

    t = name[0]
    if t in ('deg', 'Z', 'Zlo'):
        a = name[1]
        if a not in c:
            raise Fail('bad class')
        coef = {}
        for b in cls:
            v = var(a, b)
            if v is None:
                continue
            m = 2 if a == b else 1
            w = 1 if t == 'deg' else b
            coef[v] = coef.get(v, 0) + m * w
        if t == 'deg':
            return coef, '=', a * c[a]
        if t == 'Z':
            return coef, '<=', c[a] * (e - Mprev[n - 1 - a])
        return coef, '>=', c[a] * (e - ((n - 1 - a) * (k - 2)) // 2)
    if t == 'Man':
        S = sorted(set(name[1:]))
        if len(S) != len(name) - 1 or any(a not in c for a in S):
            raise Fail('bad Mantel set')
        N = sum(c[a] for a in S)
        coef = {}
        for i, a in enumerate(S):
            for b in S[i:]:
                v = var(a, b)
                if v is not None:
                    coef[v] = 1
        return coef, '<=', (N * N) // 4
    if t == 'cap':
        a, b = name[1], name[2]
        if not (a < b and a in c and b in c):
            raise Fail('bad cap')
        return {(a, b): 1}, '<=', c[a] * c[b]
    if t == 'cut':
        a, b = name[1], name[2]
        if a not in c or b not in c:
            raise Fail('bad cut')
        t0 = cmin(k, n, e, seq, Mprev, a, b)
        if t0 is None:
            raise Fail('cut row on failing class')
        coef = {}
        for a2 in cls:
            if a2 > b:
                continue
            v = var(a, a2)
            if v is None:
                continue
            coef[v] = coef.get(v, 0) + (2 if a2 == a else 1)
        return coef, '>=', c[a] * t0
    raise Fail(f'unknown constraint {name}')


def farkas_ok(k, n, e, seq, Mprev, mult):
    cols = {}
    tot = Fr(0)
    for name, ys in mult:
        y = Fr(ys)
        coef, sense, rhs = constraint(k, n, e, seq, Mprev, tuple(name))
        if sense == '>=' and y < 0:
            return False
        if sense == '<=' and y > 0:
            return False
        for v, a in coef.items():
            cols[v] = cols.get(v, Fr(0)) + y * a
        tot += y * rhs
    return all(x <= 0 for x in cols.values()) and tot > 0


def exclude_order(k, n, e, Mk, Mprev, Bprev, maxdeg, certs):
    dmax = None
    if maxdeg:
        if n - 1 not in Mk:
            raise Fail('maxdeg needs m_k(n-1)')
        dmax = e - Mk[n - 1]
    seqs = all_sequences(k, n, e, Mprev, Bprev, dmax)
    table = {}
    for items, cert in certs:
        table[tuple(sorted((int(d), int(cn)) for d, cn in items))] = cert
    for s in seqs:
        key = tuple(sorted(s.items()))
        if key not in table:
            raise Fail(f'e={e}: sequence {key} has no certificate')
        cert = table[key]
        if cert[0] == 'cut':
            if not cut_fails(k, n, e, s, Mprev):
                raise Fail(f'e={e}: cut claim false for {key}')
        elif cert[0] == 'lp':
            if not farkas_ok(k, n, e, s, Mprev, cert[1]):
                raise Fail(f'e={e}: Farkas certificate invalid for {key}')
        else:
            raise Fail('unknown sequence certificate')
    return len(seqs)


# ------------------------------------------------------------ rows
STATS = {'seq_orders': 0, 'sequences': 0}


def verify_row(k, n, m, just, Mk, Mprev, Bprev, back3):
    t = just[0]
    if t == 'back3':
        return k in back3 and n in back3[k] and m <= back3[k][n]
    if t == 'seq':
        e0, inner, maxdeg, excl = just[1], just[2], just[3], just[4]
        if not verify_row(k, n, e0, inner, Mk, Mprev, Bprev, back3):
            return False
        for e in range(e0, m):
            if str(e) not in excl:
                raise Fail(f'seq: no data for e={e}')
            STATS['sequences'] += exclude_order(k, n, e, Mk, Mprev, Bprev, maxdeg, excl[str(e)])
            STATS['seq_orders'] += 1
        return True
    return C1.verify_row(k, n, m, just, Mk, Mprev, Bprev)


def verify_cap(k, n, just, Mk, Mprev, Bprev, back3, survey):
    t = just[0]
    if t == 'survey':
        return survey.get(k) == n
    if t == 'seq-infeasible':
        e0, inner, maxdeg, excl = just[1], just[2], just[3], just[4]
        if not verify_row(k, n, e0, inner, Mk, Mprev, Bprev, back3):
            return False
        for e in range(e0, n * (k - 1) // 2 + 1):
            if str(e) not in excl:
                raise Fail(f'seq-infeasible: no data for e={e}')
            STATS['sequences'] += exclude_order(k, n, e, Mk, Mprev, Bprev, maxdeg, excl[str(e)])
            STATS['seq_orders'] += 1
        return True
    if t == 'edges>max':
        # m_k(n) >= b from the stated inner justification exceeds n(k-1)/2
        b, inner = just[1], just[2]
        return verify_row(k, n, b, inner, Mk, Mprev, Bprev, back3) and 2 * b > n * (k - 1)
    return C1.verify_cap(k, n, just, Mk, Mprev, Bprev)


def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('cert')
    ap.add_argument('--r310', type=int, default=41)
    ap.add_argument('--override', action='append', default=[],
                    help='k,n,value: override an input value at level k<=10, or a Backelin value (negative controls)')
    ap.add_argument('--claim', action='append', default=[])
    ap.add_argument('--no-back3', action='store_true')
    ap.add_argument('--no-survey', action='store_true')
    args = ap.parse_args()
    tables, caps = C1.parse_inputs(args.r310)
    back3, survey = read_cited()
    if args.no_back3:
        back3 = {}
    if args.no_survey:
        survey = {}
    cert = json.load(open(args.cert))
    uses = cert.get('uses', [])
    if 'back3' in uses and 10 in back3:
        for n, v in back3[10].items():
            if n in tables[10]:
                tables[10][n] = max(tables[10][n], v)
    for o in args.override:
        k, n, v = map(int, o.split(','))
        if k <= 10:
            tables[k][n] = v
        else:
            back3.setdefault(k, {})[n] = v
    M, B = dict(tables), dict(caps)
    nrows = 0
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
            try:
                ok = verify_row(k, n, m, just, Mk, Mprev, Bprev, back3)
            except Fail as ex:
                print(f'REJECT k={k} n={n} m={m}: {ex}')
                return 1
            if not ok:
                print(f'REJECT k={k} n={n} m={m} just={str(just)[:200]}')
                return 1
            Mk[n] = m
            nrows += 1
        n, m, just = rows[-1]
        try:
            ok = verify_cap(k, n, just, Mk, Mprev, Bprev, back3, survey)
        except Fail as ex:
            print(f'REJECT cap k={k} n={n}: {ex}')
            return 1
        if not ok:
            print(f'REJECT cap k={k} n={n} just={str(just)[:200]}')
            return 1
        M[k], B[k] = Mk, Bk
        print(f'k={k}: R(3,{k}) <= {Bk} verified ({just[0]})', flush=True)
    for c in args.claim:
        k, b = map(int, c.split(','))
        if B.get(k, 10**9) > b:
            print(f'CLAIM FAILED: R(3,{k}) <= {b} not established (have {B.get(k)})')
            return 1
    print(f"ACCEPT: {nrows} rows; {STATS['seq_orders']} (k,n,e) triples excluded by enumeration, "
          f"{STATS['sequences']} degree sequences certified")
    return 0


if __name__ == '__main__':
    sys.exit(main())
