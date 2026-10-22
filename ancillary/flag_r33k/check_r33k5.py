#!/usr/bin/env python3
r"""Independent exact checker for five-vertex flag certificates for (3,3,k;n)-colourings.

Written from the definitions; imports nothing from src/.  It shares the Ramsey inputs and the bookkeeping of
check_r33k.py (R2, R33, VERIFIED_M, ramsey), so that it can be run inside the same chain.

Setting.  c is a (3,3,k;n)-colouring (n >= 6).  Choose an ordered 5-tuple (x0,...,x4) of distinct vertices uniformly
and, independently, a uniform bijection sigma of {R,B}.  The labelled colouring K of K5 so obtained has a law
invariant under S5 x Z2 and supported on the labelled colourings with no R and no B triangle.

A certificate lists
  * star coefficients y_s for the patterns s = (c01,c02,c03,c04) of the 4-star at x0;
  * rows with multipliers mu >= 0, each a function g of K and beta of the degree profile with E[g] <= E_v[beta]:
      'up'  (pi, X, a): pi a labelled colouring of the K4 on x0..x3 (colours of 01,02,03,12,13,23), X a subset of
            {x0,..,x3}, a colours on X; S = intersection of N_{a_x}(x) over x in X;
            g = 1[K|{x0..x3} = pi] (1[x4 in S] - q/(n-4)),  q = (R(3-m_R, 3-m_B, k-m_G) - 1) - #{y not in X: y in S},
            m_c = the largest Y within X, a_y = c on Y, that is a colour-c clique under pi.  Given x0..x3, x4 is
            uniform among the other n-4 vertices and |S \ {x0..x3}| <= q, since a colour-c clique of order t_c - m_c
            in S would extend by Y.
      'low' (pi, (x,), (c,)): g = 1[pi](q/(n-4) - 1[x4 in N_c(x)]), q = (n-1-sum_{c' != c} D_c') - #{y != x: y in N_c(x)};
      'floor_up', 'floor_low', 'rec': as in check_r33k.py (events on x0,x1,x2; the same beta);
  * squares with weights lam >= 0, each Q = E[(...)^2] >= 0 written as E[q(K)]:
      'edge'  root r, const a0, a(c(x0,w),c(x1,w)):  Q = E[1[c01=r](a0 + Z/(n-2))^2], Z = sum over w != x0,x1;
              q = 1[c01=r](a0^2 + 2a0 A2 + A2^2/(n-2) + (n-3)/(n-2) A2 A3),  Aj = a(c0j, c1j);
      'triangle' tau = (c01,c02,c12), const a0, a(c(x0,w),c(x1,w),c(x2,w)):  Q = E[1[tau](a0 + Z/(n-3))^2];
              q = 1[tau](a0^2 + 2a0 A3 + A3^2/(n-3) + (n-4)/(n-3) A3 A4),  Aj = a(c0j, c1j, c2j);
      'vertex' const a0, a(c(x0,w),c(x0,w'),c(w,w')):  Q = E[(a0 + Z/N1)^2], Z = sum over ordered pairs (w,w') of
              distinct vertices other than x0, N1 = (n-1)(n-2); with Aij = a(c0i, c0j, cij),
              q = a0^2 + 2a0 A12 + [(n-3)(n-4)A12 A34 + (n-3)(A12A13 + A12A31 + A12A23 + A12A32) + A12^2 + A12A21]/N1
              (the pairs of ordered pairs are disjoint, share one vertex in one of four ways, or share both).
Phi = sum_s y_s 1[s] - sum mu g + sum lam q.  Valid if
  (1) Sym Phi(K) <= 0 for every labelled K5 colouring K with no R or B triangle (Sym = average over S5 x Z2, i.e. the
      average of Phi over the orbit of K);
  (2) J(d) = sum_s y_s P(s|d) - sum mu beta(d) > 0 at every admissible ordered profile (exclusion), or
  (2') (n-1)J(d) + d_R + d_B >= h* at every admissible ordered profile (density; m = ceil(n h*/2) <= that),
where P(s|d) is the average over sigma of the falling product (d_{s1})(d_{s2}-..)(d_{s3}-..)(d_{s4}-..)/((n-1)_4).
Then 0 >= E[Phi] >= E_v[J(d(v))], as in check_r33k.py.

Usage: python3 check_r33k5.py cert.json [...]   (checked in order; a valid exclusion for (k,n) lowers the bound used
for R(3,3,k) in later certificates; in a chain, call check(cert) after the earlier certificates)
"""
import json, sys
from fractions import Fraction as Fr
from itertools import combinations, permutations, product
import check_r33k as C

E5 = list(combinations(range(5), 2))
EI = {e: i for i, e in enumerate(E5)}
E4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
COL = {'R': 0, 'B': 1, 'G': 2}

def col(K, i, j): return K[EI[(min(i, j), max(i, j))]]

def valid(K):
    for t in combinations(range(5), 3):
        cs = {col(K, p, q) for p, q in combinations(t, 2)}
        if len(cs) == 1 and min(cs) < 2: return False
    return True

def orbits():
    """the S5 x Z2 orbits of valid labelled K5 colourings (lists of labelled colourings)."""
    allv = [K for K in product(range(3), repeat=10) if valid(K)]
    seen = set(); out = []
    group = [(p, sw) for p in permutations(range(5)) for sw in (0, 1)]
    for K in allv:
        if K in seen: continue
        orb = set()
        for p, sw in group:
            img = []
            for (i, j) in E5:
                c = col(K, p[i], p[j])
                if sw and c < 2: c = 1 - c
                img.append(c)
            orb.add(tuple(img))
        seen |= orb; out.append(sorted(orb))
    assert len(seen) == len(allv)
    return out, len(allv)

def g3(row, K):
    """the three-vertex rows (events on x0, x1, x2)."""
    kind = row[0]
    if kind in ('floor_up', 'floor_low'):
        ind = 1 if (col(K, 0, 1) == row[1] and col(K, 0, 2) == row[1] and col(K, 1, 2) == row[2]) else 0
        return Fr(ind if kind == 'floor_up' else -ind)
    return Fr(-1 if (col(K, 0, 1) == 2 and col(K, 0, 2) == 2 and col(K, 1, 2) < 2) else 0)

def g_up(kind, X, a, q, n, K):
    """the 'up'/'low' row value given that K restricted to x0..x3 is the row's pi."""
    ev = 1 if all(col(K, x, 4) == ax for x, ax in zip(X, a)) else 0
    return (ev - Fr(q, n - 4)) if kind == 'up' else (Fr(q, n - 4) - ev)

def sq(s, K, n):
    """q(K) of a square s = (lam, type, data, a0, a)."""
    lam, typ, data, a0, a = s
    if typ == 'edge':
        if col(K, 0, 1) != data: return Fr(0)
        A2 = a.get((col(K, 0, 2), col(K, 1, 2)), 0); A3 = a.get((col(K, 0, 3), col(K, 1, 3)), 0)
        return a0 * a0 + 2 * a0 * A2 + Fr(1, n - 2) * A2 * A2 + Fr(n - 3, n - 2) * A2 * A3
    if typ == 'triangle':
        if (col(K, 0, 1), col(K, 0, 2), col(K, 1, 2)) != data: return Fr(0)
        A3 = a.get((col(K, 0, 3), col(K, 1, 3), col(K, 2, 3)), 0); A4 = a.get((col(K, 0, 4), col(K, 1, 4), col(K, 2, 4)), 0)
        return a0 * a0 + 2 * a0 * A3 + Fr(1, n - 3) * A3 * A3 + Fr(n - 4, n - 3) * A3 * A4
    def A(i, j): return a.get((col(K, 0, i), col(K, 0, j), col(K, i, j)), 0)
    A12 = A(1, 2)
    inner = (n - 3) * (n - 4) * A12 * A(3, 4) + (n - 3) * (A12 * A(1, 3) + A12 * A(3, 1) + A12 * A(2, 3) + A12 * A(3, 2)) + A12 * A12 + A12 * A(2, 1)
    return a0 * a0 + 2 * a0 * A12 + Fr(inner, 1) / ((n - 1) * (n - 2))

def row_q(kind, pi, X, a, k, dmin):
    """the constant q of an 'up' or 'low' row (see the docstring)."""
    T = {e: pi[i] for i, e in enumerate(E4)}
    def tc(p, q): return T[(min(p, q), max(p, q))]
    known = sum(1 for y in range(4) if y not in X and all(tc(x, y) == ax for x, ax in zip(X, a)))
    if kind == 'up':
        m = []
        for c in range(3):
            Y = [x for x, ax in zip(X, a) if ax == c]
            best = 0
            for s in range(1, len(Y) + 1):
                for sub in combinations(Y, s):
                    if all(tc(p, q) == c for p, q in combinations(sub, 2)): best = max(best, s)
            m.append(best)
        return C.ramsey((3 - m[0], 3 - m[1], k - m[2])) - 1 - known
    assert len(X) == 1
    return dmin[a[0]] - known

def orbit_sum_int(O, ystar, rows_pi, rows3, squares, n):
    """sum of Phi over the labelled colourings K in O, computed as integer counts per term (the same linear
    combination as Phi, with integer square coefficients; equal to sum(Phi(K) for K in O))."""
    nstar = {}; ev = {}; base = {}; g3c = [0] * len(rows3); num = [0] * len(squares)
    N1 = (n - 1) * (n - 2)
    sqi = [(typ, data, int(a0), {kk: int(v) for kk, v in a.items()}) for lam, typ, data, a0, a in squares]
    for K in O:
        st = (col(K, 0, 1), col(K, 0, 2), col(K, 0, 3), col(K, 0, 4)); nstar[st] = nstar.get(st, 0) + 1
        pi = tuple(col(K, i, j) for i, j in E4)
        for idx, (mu, kind, X, a, q) in enumerate(rows_pi.get(pi, ())):
            base[(pi, idx)] = base.get((pi, idx), 0) + 1
            if all(col(K, x, 4) == ax for x, ax in zip(X, a)): ev[(pi, idx)] = ev.get((pi, idx), 0) + 1
        for i, (mu, row) in enumerate(rows3):
            g3c[i] += int(g3(row, K))
        for i, (typ, data, a0, a) in enumerate(sqi):
            if typ == 'edge':
                if col(K, 0, 1) != data: continue
                A2 = a.get((col(K, 0, 2), col(K, 1, 2)), 0); A3 = a.get((col(K, 0, 3), col(K, 1, 3)), 0)
                num[i] += (n - 2) * (a0 * a0 + 2 * a0 * A2) + A2 * A2 + (n - 3) * A2 * A3
            elif typ == 'triangle':
                if (col(K, 0, 1), col(K, 0, 2), col(K, 1, 2)) != data: continue
                A3 = a.get((col(K, 0, 3), col(K, 1, 3), col(K, 2, 3)), 0); A4 = a.get((col(K, 0, 4), col(K, 1, 4), col(K, 2, 4)), 0)
                num[i] += (n - 3) * (a0 * a0 + 2 * a0 * A3) + A3 * A3 + (n - 4) * A3 * A4
            else:
                def A(p, q): return a.get((col(K, 0, p), col(K, 0, q), col(K, p, q)), 0)
                A12 = A(1, 2)
                num[i] += N1 * (a0 * a0 + 2 * a0 * A12) + (n - 3) * (n - 4) * A12 * A(3, 4) + (n - 3) * (A12 * A(1, 3) + A12 * A(3, 1) + A12 * A(2, 3) + A12 * A(3, 2)) + A12 * A12 + A12 * A(2, 1)
    tot = sum((ystar.get(st, Fr(0)) * c for st, c in nstar.items()), Fr(0))
    for (pi, idx), b in base.items():
        mu, kind, X, a, q = rows_pi[pi][idx]; e = ev.get((pi, idx), 0)
        tot -= mu * ((e - Fr(q * b, n - 4)) if kind == 'up' else (Fr(q * b, n - 4) - e))
    for i, (mu, row) in enumerate(rows3): tot -= mu * g3c[i]
    dens = {'edge': n - 2, 'triangle': n - 3, 'vertex': N1}
    for i, s in enumerate(squares): tot += s[0] * Fr(num[i], dens[s[1]])
    return tot

_ORBITS = None

def check(cert, verbose=True, slow=False, compare=False):
    global _ORBITS
    k, n = cert['k'], cert['n']
    assert cert.get('model') == 'five-vertex' and n >= 6
    ctx = C.Context(k, n)            # D, C, dmin, ff2 from the current R2/R33 (exactly as in check_r33k)
    D = ctx.D; dmin = ctx.dmin
    ff4 = (n - 1) * (n - 2) * (n - 3) * (n - 4)
    ystar = {tuple(COL[c] for c in s): Fr(v) for s, v in cert['star'].items()}
    assert all(len(s) == 4 for s in ystar)
    rows_pi = {}; rows3 = []
    for r in cert['rows']:
        mu = Fr(r['mu']); assert mu >= 0, 'negative multiplier'
        kind = r['kind']
        if kind in ('up', 'low'):
            pi = tuple(COL[c] for c in r['pi']); X = tuple(r['X']); a = tuple(COL[c] for c in r['a'])
            assert len(pi) == 6 and len(X) == len(a) >= 1 and len(set(X)) == len(X) and all(0 <= x <= 3 for x in X)
            q = row_q(kind, pi, X, a, k, dmin)
            # a weaker constant is also valid: q' >= q for 'up' (a larger cap), q' <= q for 'low'
            assert (r['q'] >= q) if kind == 'up' else (r['q'] <= q), ('cap constant not justified', r, q)
            q = r['q']
            rows_pi.setdefault(pi, []).append((mu, kind, X, a, q))
        elif kind in ('floor_up', 'floor_low'):
            rows3.append((mu, (kind, COL[r['i']], COL[r['j']])))
        elif kind == 'rec':
            mt = {}
            for g, val in r['m'].items():
                g = int(g); val = int(val)
                if g > ctx.D[2]: continue          # green degree not admissible: the value is never used
                triv = C.ceil_half(g * max(0, g - 1 - ctx.C[2][2]))
                assert val <= max(triv, C.VERIFIED_M.get((k - 1, g), 0)), ('unjustified m value', g, val)
                mt[g] = val
            rows3.append((mu, ('rec', mt)))
        else:
            raise ValueError(kind)
    squares = []
    for s in cert['squares']:
        lam = Fr(s['lam']); assert lam >= 0
        a = {tuple(COL[c] for c in key): Fr(v) for key, v in s['a'].items()}
        typ = s['type']
        if typ == 'edge': squares.append((lam, 'edge', COL[s['root']], Fr(s['const']), a))
        elif typ == 'triangle': squares.append((lam, 'triangle', tuple(COL[c] for c in s['tau']), Fr(s['const']), a))
        elif typ == 'vertex': squares.append((lam, 'vertex', None, Fr(s['const']), a))
        else: raise ValueError(typ)

    def Phi(K):
        val = ystar.get((col(K, 0, 1), col(K, 0, 2), col(K, 0, 3), col(K, 0, 4)), Fr(0))
        pi = tuple(col(K, i, j) for i, j in E4)
        for mu, kind, X, a, q in rows_pi.get(pi, ()): val -= mu * g_up(kind, X, a, q, n, K)
        for mu, row in rows3: val -= mu * g3(row, K)
        for s in squares: val += s[0] * sq(s, K, n)
        return val

    if _ORBITS is None: _ORBITS = orbits()
    orbs, nvalid = _ORBITS
    integral = all(s[3].denominator == 1 and all(v.denominator == 1 for v in s[4].values()) for s in squares)
    worst = None
    for O in orbs:
        if slow or not integral:
            tot = sum((Phi(K) for K in O), Fr(0))
        else:
            tot = orbit_sum_int(O, ystar, rows_pi, rows3, squares, n)
            if compare: assert tot == sum((Phi(K) for K in O), Fr(0)), 'fast and direct orbit sums differ'
        s = tot / len(O)
        worst = s if worst is None else max(worst, s)
    ok1 = worst <= 0

    def star_p(s, d):
        def ff(dd):
            dd = list(dd); v = 1
            for c in s: v *= dd[c]; dd[c] -= 1
            return v
        return Fr(ff(d) + ff((d[1], d[0], d[2])), 2 * ff4)
    def J(d):
        return sum((y * star_p(s, d) for s, y in ystar.items()), Fr(0)) - sum((mu * ctx.beta(row, d) for mu, row in rows3), Fr(0))
    profs = list(ctx.profiles())
    dens = cert.get('type', 'exclusion') == 'density'
    if not dens:
        minJ = min((J(d) for d in profs), default=None)
        ok2 = (minJ is None) or minJ > 0
    else:
        hst = Fr(cert['hstar'])
        hmin = min(((n - 1) * J(d) + d[0] + d[1] for d in profs), default=None)
        ok2 = (hmin is None) or (hmin >= hst and int(cert['m']) <= C.ceil_frac(n * hst / 2))
    if verbose:
        what = f"every (3,3,{k};{n})-colouring has e(H) >= {cert['m']}" if dens else f"R(3,3,{k}) <= {n}"
        print(f"{what} [five-vertex]: D = {D}; {sum(len(v) for v in rows_pi.values()) + len(rows3)} rows, {len(squares)} squares")
        print(f"  (1) max Sym Phi over {len(orbs)} orbits ({nvalid} labelled K5 colourings) = {float(worst):.4e} -> {'OK' if ok1 else 'FAIL'}")
        if dens: print(f"  (2') min (n-1)J + h over {len(profs)} profiles = {float(hmin) if hmin is not None else None} >= h* = {float(hst):.5f} -> {'OK' if ok2 else 'FAIL'}")
        else: print(f"  (2) min J over {len(profs)} profiles = {float(minJ) if minJ is not None else None} -> {'OK' if ok2 else 'FAIL'}")
    return ok1 and ok2

if __name__ == '__main__':
    allok = True
    for path in sys.argv[1:]:
        cert = json.load(open(path))
        try: ok = check(cert)
        except (AssertionError, KeyError) as e: print('  assertion failed:', e); ok = False
        print(f"{path}: {'VALID' if ok else 'REJECTED'}")
        # as in check_r33k.py: a valid exclusion lowers the bound used for R(3,3,k) in the certificates after it
        if ok and cert.get('type', 'exclusion') == 'exclusion': C.R33[cert['k']] = min(C.R33[cert['k']], cert['n'])
        if ok and cert.get('type') == 'density':
            C.VERIFIED_M[(cert['k'], cert['n'])] = max(C.VERIFIED_M.get((cert['k'], cert['n']), 0), int(cert['m']))
        allok &= ok
    print('ALL VALID' if allok else 'SOME REJECTED')
    sys.exit(0 if allok else 1)
