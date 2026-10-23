#!/usr/bin/env python3
"""Exact checker for the unified chain: flag certificates (checked by check_r33k.py) interleaved, level by level,
with the rows of the ladder of Section 5 of the paper.  Standard library only; imports nothing from src/.

Definitions (Section 3 of the paper), for a (3,3,k;n)-colouring with red-or-blue graph H:
  D = R(3,k) - 1 caps the red and the blue degree; B_{k-1} >= R(3,3,k-1) is the bound proved earlier in the chain,
  so every H-degree h is admissible: max(0, n - B_{k-1}) <= h <= min(n - 1, 2D).
  A(h) = max over r with 0 <= r, h - r <= D of floor((k-1) r / 2) + floor((k-1)(h - r) / 2)   (apex bound, Lemma 3.1),
  p(h) = 3(k-1)h - 6A(h) >= 0,
  F(h)   = 3h^2 + (U + 5 - 3n - 3k)h + (n - U - 1)(n - 1) + p(h),  U = B_{k-2} >= R(3,3,k-2)   (Lemma 3.2),
  Psi(h) = h(2h - n - 3(k-1)) + 2 m_{k-1}(n - 1 - h) + p(h)                                    (Lemma 3.3),
  and sum_v f(h_v) <= 0 for f in {F, Psi}.
A row (k, n) claims a valid lower bound m_k(n) on e(H).  The checker accepts it if it is at most the largest of
  * ceil(n h_min / 2)  (every H-degree is at least h_min);
  * for f in {F, Psi} with a recorded pair h' < h'' of admissible degrees: the line through (h', f(h')) and
    (h'', f(h'')), if its slope is negative and it lies below f at every admissible h, gives ceil(n alpha/(2 beta))
    (Lemma 3.4(a), line alpha - beta h);
  * m_k(n-1) + max(0, n - B_{k-1})  and  ceil(m_k(s) n(n-1)/(s(s-1))) for 2 <= s < n   (Lemma 3.5);
  * a value proved for (k, n) by a flag density certificate verified earlier in the chain.
m_{k-1}(z) in Psi is the value accepted earlier in the chain (m_2(z) = C(z,2) for z <= 5; m(0) = m(1) = 0).
The bound B_k (k >= 6) is accepted if, at n = B_k, F or Psi is positive at every admissible h (Lemma 3.4(b)), or a
valid lower bound on e(H) at n = B_k (as above) exceeds n h_max / 2, or a flag exclusion certificate for some
order <= B_k at level k was verified earlier in the chain.  For k <= 5, B_k is the input (17, 30, 57).
Flag certificates with "model": "five-vertex" are checked by check_r33k5.py (same shared state).
Every accepted m_k(n) becomes available to the 'rec' rows of later flag certificates (check_r33k.VERIFIED_M), and
every accepted B_k to their constants (check_r33k.R33).  R33[k] for k >= 6 starts at infinity, so every bound used
is proved in the chain.

Usage: python3 check_unified.py [certificates/unified/chain_final.json]   (flag certificate paths are relative to
the parent of the chain file's directory, here certificates/)
"""
import json, os, sys, hashlib
from fractions import Fraction as Fr
import check_r33k as C
import check_r33k5 as C5

INF = 10 ** 9
INPUT = {1: 1, 2: 6, 3: 17, 4: 30, 5: 57}

def ceil_frac(q):
    q = Fr(q); return -((-q.numerator) // q.denominator)

def A(k, h, D):
    return max(((k - 1) * r) // 2 + ((k - 1) * (h - r)) // 2 for r in range(max(0, h - D), min(h, D) + 1))

def m_of(k1, z):
    if z <= 1: return 0
    return C.VERIFIED_M[(k1, z)]          # KeyError if the chain has not proved a value here

def fvals(k, n, Bk1, Bk2):
    D = C.R2[k] - 1
    hmin, hmax = max(0, n - Bk1), min(n - 1, 2 * D)
    F, P = {}, {}
    for h in range(hmin, hmax + 1):
        p = 3 * (k - 1) * h - 6 * A(k, h, D)
        assert p >= 0
        U = Bk2
        F[h] = 3 * h * h + (U + 5 - 3 * n - 3 * k) * h + (n - U - 1) * (n - 1) + p
        P[h] = h * (2 * h - n - 3 * (k - 1)) + 2 * m_of(k - 1, n - 1 - h) + p
    return hmin, hmax, F, P

def line_bound(n, f, pair):
    h1, h2 = pair
    assert h1 < h2 and h1 in f and h2 in f, ('line ends not admissible', pair)
    slope = Fr(f[h2] - f[h1], h2 - h1)
    if slope >= 0: return None
    alpha = f[h1] - slope * h1; beta = -slope
    assert all(alpha - beta * h <= v for h, v in f.items()), ('line not below f', pair)
    return ceil_frac(Fr(n) * alpha / (2 * beta))

def candidates(k, n, row, Tk, Bk1, Bk2):
    hmin, hmax, F, P = fvals(k, n, Bk1, Bk2)
    c = {}
    if hmin <= hmax: c['hmin'] = ceil_frac(Fr(n * hmin, 2))
    for key, f in (('F', F), ('Psi', P)):
        if row is not None and row.get(key):
            b = line_bound(n, f, row[key])
            if b is not None: c[key] = b
    if n - 1 in Tk: c['delete'] = Tk[n - 1] + max(0, n - Bk1)
    c['subset'] = max([ceil_frac(Fr(Tk[s] * n * (n - 1), s * (s - 1))) for s in range(2, n) if s in Tk] + [0])
    c['flag'] = C.VERIFIED_M.get((k, n), 0)
    return c, (hmin, hmax, F, P)

_MEMO = {}
def run_flag(path, base):
    """check a flag certificate in the current state.  Its verdict depends only on its content, on R2/R33 and on the
    values VERIFIED_M at level k-1 (its rec row), so verdicts are memoised on exactly these (used by the controls,
    which re-run the chain many times)."""
    raw = open(os.path.join(base, path), 'rb').read()
    cert = json.loads(raw)
    k = cert['k']
    key = (hashlib.sha256(raw).hexdigest(), tuple(sorted(C.R33.items())), tuple(sorted(C.R2.items())),
           tuple(sorted((z, v) for (kk, z), v in C.VERIFIED_M.items() if kk == k - 1)))
    if key in _MEMO:
        ok = _MEMO[key]
    else:
        try:
            ok = (C5.check(cert, verbose=False) if cert.get('model') == 'five-vertex' else C.check(cert, verbose=False))
        except (AssertionError, KeyError, ValueError) as e:
            print('  flag certificate assertion:', path, e); ok = False
        _MEMO[key] = ok
    if ok and cert.get('type', 'exclusion') == 'exclusion': C.R33[cert['k']] = min(C.R33[cert['k']], cert['n'])
    if ok and cert.get('type') == 'density':
        C.VERIFIED_M[(cert['k'], cert['n'])] = max(C.VERIFIED_M.get((cert['k'], cert['n']), 0), int(cert['m']))
    return ok, cert

def main(chain_path, verbose=True, kmax=15, failfast=False):
    base = os.path.join(os.path.dirname(os.path.abspath(chain_path)), '..')
    chain = json.load(open(chain_path))
    for k in range(6, 16): C.R33[k] = INF
    C.VERIFIED_M.clear()
    for z in range(6): C.VERIFIED_M[(2, z)] = z * (z - 1) // 2
    allok = True; nrows = 0; ndeg = 0; nflag = 0
    prev_k = 2
    for lev in chain['levels']:
        k = lev['k']; assert k == prev_k + 1, 'levels out of order'; prev_k = k
        if k > kmax or (failfast and not allok): break
        for p in lev['flag']:
            ok, cert = run_flag(p, base); nflag += 1
            assert cert['k'] == k, ('flag certificate at the wrong level', p)
            if not ok: print('  REJECTED flag certificate', p); allok = False
        Bk1, Bk2 = C.R33[k - 1], C.R33[k - 2]
        assert Bk1 < INF and Bk2 < INF
        Bk = lev['B']
        Tk = {0: 0, 1: 0}
        for n in range(2, Bk):
            row = lev['rows'][str(n)]
            try:
                c, (hmin, hmax, F, P) = candidates(k, n, row, Tk, Bk1, Bk2)
            except (AssertionError, KeyError) as e:
                print(f'  row k={k} n={n}: assertion {e}'); allok = False
                c, (hmin, hmax, F, P) = candidates(k, n, None, Tk, Bk1, Bk2)
            ndeg += len(F); nrows += 1
            if not row['m'] <= max(c.values()):
                print(f'  row k={k} n={n}: claimed {row["m"]} > {max(c.values())} {c}'); allok = False
            Tk[n] = row['m']
            C.VERIFIED_M[(k, n)] = max(C.VERIFIED_M.get((k, n), 0), row['m'])
        # the exclusion of B_k
        if k in INPUT:
            assert Bk == INPUT[k], 'input bound changed'; how = 'input'
        else:
            meth = lev['excl']['method']; n = Bk
            c, (hmin, hmax, F, P) = candidates(k, n, None, Tk, Bk1, Bk2)
            if meth == 'F': ok = all(v > 0 for v in F.values())
            elif meth == 'Psi': ok = all(v > 0 for v in P.values())
            elif meth == 'edges': ok = 2 * max(c.values()) > n * hmax
            elif meth == 'flag': ok = C.R33[k] <= Bk
            else: ok = False
            how = meth
            if meth in ('F', 'Psi'):
                f = F if meth == 'F' else P
                how = f'{meth} > 0 at all {len(f)} admissible h in [{hmin},{hmax}], min {min(f.values()) if f else None}'
            if not ok: print(f'  exclusion of B_{k} = {Bk} by {meth}: FAILED'); allok = False
        C.R33[k] = min(C.R33[k], Bk)
        if verbose: print(f'k={k}: R(3,3,{k}) <= {C.R33[k]} ({how}); {Bk - 2} rows, {len(lev["flag"])} flag certificates', flush=True)
    print(f'{nflag} flag certificates, {nrows} ladder rows, {ndeg} admissible degree cases')
    print('CHAIN VALID' if allok else 'CHAIN REJECTED')
    print('bounds:', {k: C.R33[k] for k in range(3, 16)})
    return allok

if __name__ == '__main__':
    default = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'certificates', 'unified', 'chain_final.json')
    sys.exit(0 if main(sys.argv[1] if len(sys.argv) > 1 else default) else 1)
