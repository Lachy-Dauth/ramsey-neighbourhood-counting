#!/usr/bin/env python3
"""Independent exact checker for four-vertex flag certificates  R(3,3,k) <= n.

Written from the definitions; it imports nothing from the search code in src/.  Python standard library only.

Setting.  c is a (3,3,k;n)-colouring: colours R, B (both triangle-free) and G (no K_k).  Choose an ordered
quadruple (x0,x1,x2,x3) of distinct vertices uniformly and, independently, a uniform bijection sigma of
{R,B} (G fixed).  The labelled colouring K of K4 so obtained has a law invariant under S4 x Z2 (Z2 swaps
the labels R and B), supported on labelled colourings with no R and no B triangle.

A certificate lists
  * star coefficients y_s for the patterns s = (c01,c02,c03) of the star at x0;
  * rows with multipliers mu >= 0.  Each row is a function g of K and a function beta of the degree profile
    with E[g] <= E_v[beta(d(v))] in every (3,3,k;n)-colouring.  The checker recomputes every constant:
      'up'  (tau, X, a): g = 1[tau](1[x3 in S] - q/(n-3)), beta = 0, where tau = (c01,c02,c12),
            S = intersection over x in X of N_{a_x}(x) (X a subset of {x0,x1,x2}),
            q = (R(3-m_R, 3-m_B, k-m_G) - 1) - #{y in {x0,x1,x2} - X : y in S},
            m_c = largest Y within X with a_y = c for y in Y that is a colour-c clique; a colour-c clique on
            t_c - m_c vertices of S would extend by Y.  For |X| = 1 this is the degree cap D_c.
      'low' (tau, (x,), (c,)): g = 1[tau](q/(n-3) - 1[x3 in N_c(x)]), beta = 0,
            q = (n-1-sum_{c' != c} D_c') - #{y in {x0,x1,x2} - {x} : y in N_c(x)}.
      'floor_up'  (i,j): g = 1[c01=c02=i, c12=j], beta = 2 floor(C_ij d_i / 2)/((n-1)(n-2))     (Cor. 2.2)
      'floor_low' (i,j): g = -1[c01=c02=i, c12=j],
                         beta = -2 ceil(d_i max(0, d_i-1-sum_{j' != j} C_ij') / 2)/((n-1)(n-2))
      'rec'            : g = -1[c01=c02=G, c12 in {R,B}],  beta = -2 m(d_G)/((n-1)(n-2)), since
            N_G(v) carries a (3,3,k-1;d_G)-colouring and e_H(N_G(v)) >= m(d_G).  The certificate lists m(g);
            each value is accepted only if it is at most ceil(g max(0, g-1-C_GG)/2) (each u in N_G(v) has at
            most C_GG green neighbours in N_G(v)) or at most a bound for (3,3,k-1;g)-colourings proved by a
            density certificate verified earlier in the same run;
    with D_c = R(t-e_c) - 1 and C_ij = R(t-e_i-e_j) - 1 (Lemma 2.1), t = (3,3,k), and beta averaged over
    the label map sigma (d_i is the degree in the colour carrying label i).  A recorded 'up' constant q may exceed,
    and a 'low' constant may fall short of, the recomputed one (a weaker row is still valid);
  * squares with weights lam >= 0: root colour r, constant a0 and a function a of the pair
    (c(x0,w), c(x1,w)).  Q = E[1[c01=r](a0 + Z/(n-2))^2] >= 0, Z = sum of a_w over the n-2 vertices w other
    than x0, x1; as (x2,x3) is a uniform ordered pair of distinct such w, Q = E[q(K)] with
        q(K) = 1[c01=r](a0^2 + 2 a0 a(c02,c12) + a(c02,c12)^2/(n-2) + (n-3)/(n-2) a(c02,c12) a(c03,c13)).
Let Phi = sum_s y_s 1[s] - sum mu g + sum lam q.  The certificate is valid if
  (1) Sym Phi(K) <= 0 for every labelled K4 colouring K with no R or B triangle (Sym = average over S4 x Z2);
  (2) J(d) = sum_s y_s P(s | d) - sum mu beta(d) > 0 at every admissible ordered profile d = (d_R,d_B,d_G):
      d_R, d_B <= D_R = D_B, d_G <= D_G, d_R + d_B + d_G = n-1.  Here P(s | d) = average over sigma of
      (d_{s1})(d_{s2} - [s2=s1])(d_{s3} - [s3=s1] - [s3=s2]) / ((n-1)(n-2)(n-3)).
Then 0 >= E[Phi] >= E_v[sum_s y_s P(s | d(v))] - sum mu E_v[beta(d(v))] = E_v[J(d(v))] > 0, a contradiction.

A density certificate ("type": "density") has the same data and (1), and claims h* and m: in place of (2),
  (2') (n-1) J(d) + d_R + d_B >= h* at every admissible ordered profile d,
so that the average red-or-blue degree is at least h* - (n-1) E_v[J] >= h*, and every (3,3,k;n)-colouring has
at least m = ceil(n h*/2) red-or-blue edges.

Usage:  python3 check_r33k.py cert1.json [cert2.json ...]
Certificates are checked in order; a valid exclusion certificate for (k,n) lowers the bound used for R(3,3,k)
to n in the certificates after it, and a valid density certificate for (k,n) makes its m available to the
'rec' rows of later certificates (so a chain such as R(3,3,6) <= 87, the densities at k = 6, then k = 7, is
checked in one call).  A directory argument stands for its *.json files in the order of its manifest.txt.
"""
import json, sys
from fractions import Fraction as Fr
from itertools import permutations, product, combinations

# ---------------------------------------------------------------- inputs (Table 3 of the paper)
R2 = {3: 6, 4: 9, 5: 14, 6: 18, 7: 23, 8: 28, 9: 36, 10: 41, 11: 50, 12: 59, 13: 68, 14: 77, 15: 87}  # R(3,j) (upper bounds for j >= 10)
R33 = {1: 1, 2: 6, 3: 17, 4: 30, 5: 57,          # R(3,3,j): exact for j <= 4 (R(3,3,1) = 1, R(3,3,2) = R(3,3) = 6); 57 from (1)
       6: 88, 7: 129, 8: 179,                    # Theorems 4.1, 4.3, 4.5 of the paper (hand proofs)
       9: 247, 10: 315, 11: 407, 12: 512, 13: 628, 14: 756, 15: 901}   # Theorem 5.2 (ladder)
VERIFIED_M = {}      # (k, n) -> a lower bound on e_H proved by a density certificate checked in this run
COL = {'R': 0, 'B': 1, 'G': 2}
EDGES = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

def ramsey(s):
    """R(s_R, s_B, s_G) for s_R, s_B <= 3: R(...,1,...) = 1, an entry 2 drops (R(2,a,b) = R(a,b)), R() = 2."""
    if min(s) <= 1: return 1
    rest = sorted(x for x in s if x != 2)
    if not rest: return 2
    if len(rest) == 1: return rest[0]
    if len(rest) == 2:
        assert rest[0] == 3, rest
        return R2[rest[1]]
    assert rest[0] == 3 and rest[1] == 3, rest
    return R33[rest[2]]

def col(K, i, j): return K[EDGES.index((min(i, j), max(i, j)))]

def valid(K):
    """no R and no B triangle."""
    for tri in combinations(range(4), 3):
        cs = {col(K, p, q) for p, q in combinations(tri, 2)}
        if len(cs) == 1 and min(cs) < 2: return False
    return True

def ceil_half(x): return -((-x) // 2)
def ceil_frac(q): return -((-q.numerator) // q.denominator)

class Context:
    """constants and row functions for (3,3,k;n)-colourings."""
    def __init__(self, k, n):
        self.k, self.n = k, n
        t = (3, 3, k)
        def R_minus(*cols):
            s = list(t)
            for c in cols: s[c] -= 1
            return ramsey(s)
        self.D = [R_minus(c) - 1 for c in range(3)]
        self.C = [[R_minus(i, j) - 1 for j in range(3)] for i in range(3)]
        self.dmin = [n - 1 - sum(self.D[c2] for c2 in range(3) if c2 != c) for c in range(3)]
        self.ff2, self.ff3 = (n - 1) * (n - 2), (n - 1) * (n - 2) * (n - 3)

    def cap_q(self, tau, X, a):
        T = {(0, 1): tau[0], (0, 2): tau[1], (1, 2): tau[2]}
        m = []
        for c in range(3):
            Y = [x for x, ax in zip(X, a) if ax == c]
            best = 0
            for r in range(1, len(Y) + 1):
                for sub in combinations(Y, r):
                    if all(T[(p, q)] == c for p, q in combinations(sub, 2)): best = max(best, r)
            m.append(best)
        cap = ramsey((3 - m[0], 3 - m[1], self.k - m[2])) - 1
        return cap - self.known(tau, X, a)

    def low_q(self, tau, X, a):
        assert len(X) == 1
        return self.dmin[a[0]] - self.known(tau, X, a)

    @staticmethod
    def known(tau, X, a):
        T = {(0, 1): tau[0], (0, 2): tau[1], (1, 2): tau[2]}
        return sum(1 for y in range(3) if y not in X and all(T[(min(x, y), max(x, y))] == ax for x, ax in zip(X, a)))

    def g(self, row, K):
        """the four-vertex function of a row."""
        kind = row[0]; n = self.n
        if kind in ('up', 'low'):
            tau, X, a, q = row[1:5]
            if (col(K, 0, 1), col(K, 0, 2), col(K, 1, 2)) != tau: return Fr(0)
            ev = 1 if all(col(K, x, 3) == ax for x, ax in zip(X, a)) else 0
            return (ev - Fr(q, n - 3)) if kind == 'up' else (Fr(q, n - 3) - ev)
        if kind in ('floor_up', 'floor_low'):
            i, j = row[1], row[2]
            ind = 1 if (col(K, 0, 1) == i and col(K, 0, 2) == i and col(K, 1, 2) == j) else 0
            return Fr(ind if kind == 'floor_up' else -ind)
        if kind == 'rec':
            return Fr(-1 if (col(K, 0, 1) == 2 and col(K, 0, 2) == 2 and col(K, 1, 2) < 2) else 0)
        raise ValueError(kind)

    def beta(self, row, d):
        """the profile bound of a row, averaged over the label map sigma."""
        kind = row[0]; C = self.C
        if kind in ('up', 'low'): return Fr(0)
        tot = Fr(0)
        for dl in (d, (d[1], d[0], d[2])):           # dl[i] = degree in the colour carrying label i
            if kind == 'floor_up':
                i, j = row[1], row[2]
                tot += Fr(2 * ((C[i][j] * dl[i]) // 2), self.ff2)
            elif kind == 'floor_low':
                i, j = row[1], row[2]
                lb = max(0, dl[i] - 1 - sum(C[i][jj] for jj in range(3) if jj != j))
                tot -= Fr(2 * ceil_half(lb * dl[i]), self.ff2)
            else:
                tot -= Fr(2 * row[1][dl[2]], self.ff2)       # KeyError if the certificate omits a needed g
        return tot / 2

    def sq(self, square, K):
        lam, root, a0, a = square; n = self.n
        if col(K, 0, 1) != root: return Fr(0)
        a2 = a.get((col(K, 0, 2), col(K, 1, 2)), Fr(0)); a3 = a.get((col(K, 0, 3), col(K, 1, 3)), Fr(0))
        return a0 * a0 + 2 * a0 * a2 + a2 * a2 / (n - 2) + Fr(n - 3, n - 2) * a2 * a3

    def star_p(self, s, d):
        def ffall(dd):
            dd = list(dd); v = 1
            for c in s: v *= dd[c]; dd[c] -= 1
            return v
        return Fr(ffall(d) + ffall((d[1], d[0], d[2])), 2 * self.ff3)

    def profiles(self):
        D, n = self.D, self.n
        for dR in range(D[0] + 1):
            for dB in range(D[1] + 1):
                dG = n - 1 - dR - dB
                if 0 <= dG <= D[2]: yield (dR, dB, dG)

GROUP = [(p, sw) for p in permutations(range(4)) for sw in (0, 1)]
def act(K, p, sw):
    out = []
    for (i, j) in EDGES:
        c = col(K, p[i], p[j])
        if sw and c < 2: c = 1 - c
        out.append(c)
    return tuple(out)

def parse(cert, ctx):
    rows = []
    for r in cert['rows']:
        mu = Fr(r['mu']); assert mu >= 0, 'negative multiplier'
        kind = r['kind']
        if kind in ('up', 'low'):
            tau = tuple(COL[c] for c in r['tau']); X = tuple(r['X']); a = tuple(COL[c] for c in r['a'])
            assert len(X) == len(a) >= 1 and len(set(X)) == len(X) and all(0 <= x <= 2 for x in X)
            assert not (tau[0] == tau[1] == tau[2] < 2), 'tau has a red or blue triangle'
            q = ctx.cap_q(tau, X, a) if kind == 'up' else ctx.low_q(tau, X, a)
            # a weaker constant is also valid: q' >= q for 'up' (a larger cap), q' <= q for 'low'
            assert (r['q'] >= q) if kind == 'up' else (r['q'] <= q), ('cap constant not justified', r, q)
            q = r['q']
            rows.append((mu, (kind, tau, X, a, q)))
        elif kind in ('floor_up', 'floor_low'):
            rows.append((mu, (kind, COL[r['i']], COL[r['j']])))
        elif kind == 'rec':
            mt = {}
            for g, val in r['m'].items():
                g = int(g); val = int(val)
                if g > ctx.D[2]: continue          # green degree not admissible: the value is never used
                triv = ceil_half(g * max(0, g - 1 - ctx.C[2][2]))
                assert val <= max(triv, VERIFIED_M.get((ctx.k - 1, g), 0)), ('unjustified m value', g, val)
                mt[g] = val
            rows.append((mu, ('rec', mt)))
        else:
            raise ValueError(kind)
    squares = []
    for s in cert['squares']:
        lam = Fr(s['lam']); assert lam >= 0
        squares.append((lam, COL[s['root']], Fr(s['const']),
                        {(COL[key[0]], COL[key[1]]): Fr(v) for key, v in s['a'].items()}))
    ystar = {tuple(COL[c] for c in s): Fr(v) for s, v in cert['star'].items()}
    return rows, squares, ystar

def check(cert, verbose=True):
    k, n = cert['k'], cert['n']
    ctx = Context(k, n)
    rows, squares, ystar = parse(cert, ctx)

    def Phi(K):
        val = ystar.get((col(K, 0, 1), col(K, 0, 2), col(K, 0, 3)), Fr(0))
        for mu, row in rows: val -= mu * ctx.g(row, K)
        for s in squares: val += s[0] * ctx.sq(s, K)
        return val

    worst = None; nvalid = 0; cache = {}
    for K in product(range(3), repeat=6):
        if not valid(K): continue
        nvalid += 1
        tot = Fr(0)
        for p, sw in GROUP:
            KK = act(K, p, sw)
            if KK not in cache: cache[KK] = Phi(KK)
            tot += cache[KK]
        s = tot / len(GROUP)
        worst = s if worst is None else max(worst, s)
    ok1 = worst <= 0

    minJ = None; argmin = None; nprof = 0
    for d in ctx.profiles():
        nprof += 1
        J = sum((y * ctx.star_p(s, d) for s, y in ystar.items()), Fr(0)) - sum((mu * ctx.beta(row, d) for mu, row in rows), Fr(0))
        if minJ is None or J < minJ: minJ, argmin = J, d
    dens = cert.get('type', 'exclusion') == 'density'
    if not dens:
        ok2 = (minJ > 0) if nprof else True
    else:
        hst = Fr(cert['hstar'])
        hmin = min(((n - 1) * (sum((y * ctx.star_p(s, d) for s, y in ystar.items()), Fr(0)) - sum((mu * ctx.beta(row, d) for mu, row in rows), Fr(0))) + d[0] + d[1]
                    for d in ctx.profiles()), default=None)
        ok2 = (hmin is None) or (hmin >= hst and int(cert['m']) <= ceil_frac(n * hst / 2))
    if verbose:
        what = f"every (3,3,{k};{n})-colouring has e(H) >= {cert['m']}" if dens else f"R(3,3,{k}) <= {n}"
        print(f"{what}:  D = {ctx.D}, C = {ctx.C}; {len(rows)} rows, {len(squares)} squares")
        print(f"  (1) max Sym Phi over {nvalid} labelled K4 colourings = {float(worst):.4e}  -> {'OK' if ok1 else 'FAIL'}")
        if not nprof: print("  (2) no admissible profile")
        elif not dens: print(f"  (2) min J over {nprof} ordered profiles = {float(minJ):.4e} at {argmin}  -> {'OK' if ok2 else 'FAIL'}")
        else: print(f"  (2') min (n-1)J + h over {nprof} ordered profiles = {float(hmin):.5f} >= h* = {float(hst):.5f}, m = {cert['m']}  -> {'OK' if ok2 else 'FAIL'}")
    return ok1 and ok2

def expand(args):
    import os
    out = []
    for a in args:
        if os.path.isdir(a):
            for line in open(os.path.join(a, 'manifest.txt')):
                if line.strip() and not line.startswith('#'): out.append(os.path.join(a, line.strip()))
        else: out.append(a)
    return out

if __name__ == '__main__':
    allok = True
    for path in expand(sys.argv[1:]):
        cert = json.load(open(path))
        try:
            ok = check(cert)
        except AssertionError as e:
            print('  assertion failed:', e); ok = False
        print(f"{path}: {'VALID' if ok else 'REJECTED'}")
        if ok and cert.get('type', 'exclusion') == 'exclusion': R33[cert['k']] = min(R33[cert['k']], cert['n'])
        if ok and cert.get('type') == 'density':
            VERIFIED_M[(cert['k'], cert['n'])] = max(VERIFIED_M.get((cert['k'], cert['n']), 0), int(cert['m']))
        allok &= ok
    print('ALL VALID' if allok else 'SOME REJECTED')
    sys.exit(0 if allok else 1)
