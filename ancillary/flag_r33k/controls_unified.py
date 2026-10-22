#!/usr/bin/env python3
"""Negative and positive controls for check_unified.py.

  python3 controls_unified.py [chain.json] [nopaper-chain.json]

1. the chain is accepted, with the bounds it claims;
2. the chain built without any flag certificate (certificates/unified/chain_noflag.json, written by the search code
   from an empty flag manifest) is accepted and gives
   exactly the paper's bounds 88, 129, 179, 247, 315, 407, 512, 628, 756, 901 (Theorem 4.2 and Section 4);
3. the chain with its flag certificates removed is rejected;
4. each of several ladder rows with its m raised by one is rejected;
5. B_7 claimed one lower (126, by Psi) is rejected, and B_6 = 86 'by flag' is rejected;
6. a flag density certificate with m raised by one is rejected (hence the chain);
7. real colourings: from the paper's circulant witnesses (../circulants.json) and their iterated green
   neighbourhoods, greedy vertex deletion (always the vertex of largest H-degree) gives (3,3,j;s)-colourings of every
   order s; each has e(H) >= the accepted m_j(s) for every j >= its level that the chain covers.
Standard library only.
"""
import copy, io, json, os, sys, contextlib, tempfile
import check_unified as U
import check_r33k as C

HERE = os.path.dirname(os.path.abspath(__file__))
CIRCULANTS = os.path.join(HERE, '..', 'circulants.json')     # the paper's witnesses (Theorem 8.1)

def circulant(w):
    """colour matrix of a circulant witness: 0 red, 1 blue, 2 green, -1 on the diagonal"""
    n, A, B = w['n'], set(w['A']), set(w['B'])
    dist = lambda i, j: min((i - j) % n, (j - i) % n)
    return [[-1 if i == j else 0 if dist(i, j) in A else 1 if dist(i, j) in B else 2 for j in range(n)] for i in range(n)]

def run(chain_obj, keep=None, failfast=True):
    d = tempfile.mkdtemp(dir=os.path.join(HERE, 'certificates'))
    p = os.path.join(d, 'chain.json')
    json.dump(chain_obj, open(p, 'w'))
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        try: ok = U.main(p, verbose=False, failfast=failfast)
        except (AssertionError, KeyError, ValueError) as e: ok = False
    bounds = {k: C.R33[k] for k in range(3, 16)}
    os.remove(p); os.rmdir(d)
    return ok, bounds

def main(chain_path, nopaper_path):
    chain = json.load(open(chain_path)); res = []
    ok, b = run(chain, failfast=False); res.append((f'chain accepted, bounds {[b[k] for k in range(6, 16)]}', ok))
    claimed = {lev['k']: lev['B'] for lev in chain['levels']}
    res.append(('accepted bounds equal the claimed ones', all(b[k] == claimed[k] for k in claimed)))
    TABLE4 = [88, 129, 179, 247, 315, 407, 512, 628, 756, 901]
    ok, b = run(json.load(open(nopaper_path)), failfast=False)
    res.append((f'flag-free chain accepted with the paper bounds {[b[k] for k in range(6, 16)]}', ok and [b[k] for k in range(6, 16)] == TABLE4))
    d = copy.deepcopy(chain)
    for lev in d['levels']: lev['flag'] = []
    ok, b = run(d); res.append(('chain without its flag certificates rejected', not ok))
    rej = 0; tot = 0
    claimedB = {lev['k']: lev['B'] for lev in chain['levels']}
    for k, n in [(4, 29), (5, 49), (6, claimedB[6] - 1), (6, 70), (7, claimedB[7] - 1), (8, 150), (10, claimedB[10] - 1), (12, 400), (14, claimedB[14] - 1), (15, claimedB[15] - 1)]:
        d = copy.deepcopy(chain); lev = d['levels'][k - 3]; lev['rows'][str(n)]['m'] += 1
        ok, b = run(d); tot += 1; rej += not ok
    res.append((f'row m raised by one: {rej}/{tot} rejected', rej == tot))
    b7 = claimedB[7] - 1
    d = copy.deepcopy(chain); lev = d['levels'][7 - 3]; lev['B'] = b7; lev['excl'] = {'method': 'Psi'}; del lev['rows'][str(b7)]
    ok, b = run(d); res.append((f'B_7 = {b7} by Psi rejected', not ok))
    b6 = claimedB[6] - 1
    d = copy.deepcopy(chain); lev = d['levels'][6 - 3]; lev['B'] = b6; del lev['rows'][str(b6)]
    ok, b = run(d); res.append((f'B_6 = {b6} by flag rejected', not ok))
    # a corrupted flag density certificate
    lev6 = chain['levels'][6 - 3]; p = next(x for x in lev6['flag'] if x.startswith('k6/') and 'dens_80' in x)
    cert = json.load(open(os.path.join(HERE, 'certificates', p))); cert['m'] += 1
    tmp = os.path.join(HERE, 'certificates', 'k6', 'tmp_bad_dens_80.json'); json.dump(cert, open(tmp, 'w'))
    d = copy.deepcopy(chain); lev = d['levels'][6 - 3]; lev['flag'] = [x if x != p else 'k6/tmp_bad_dens_80.json' for x in lev['flag']]
    ok, b = run(d); os.remove(tmp); res.append(('flag density certificate with m + 1 rejected', not ok))
    # real colourings
    ok, b = run(chain, failfast=False)
    tests = 0; fails = 0; minslack = None
    for w in json.load(open(CIRCULANTS))['witnesses']:
        name, lvl = f"R_3_3_{w['k']}_n{w['n']}", w['k']
        A = circulant(w); j = lvl; S = list(range(len(A)))
        while j >= 3 and len(S) >= 2:
            Hm = [[1 if A[a][b] in (0, 1) else 0 for b in S] for a in S]       # red-or-blue adjacency of the subset
            alive = list(range(len(S))); deg = [sum(r) for r in Hm]; e = sum(deg) // 2
            while len(alive) >= 2:
                s = len(alive)
                for jj in range(j, 16):
                    if (jj, s) in C.VERIFIED_M:
                        tests += 1; sl = e - C.VERIFIED_M[(jj, s)]
                        minslack = sl if minslack is None else min(minslack, sl)
                        if sl < 0: fails += 1; print('  FAIL', name, jj, s, e, C.VERIFIED_M[(jj, s)])
                v = max(alive, key=lambda x: deg[x]); alive.remove(v)
                e -= deg[v]; deg = [d - h for d, h in zip(deg, Hm[v])]; deg[v] = 0
            # next: green neighbourhood of the first vertex, a (3,3,j-1)-colouring
            v = S[0]; S = [u for u in S if u != v and A[v][u] == 2]; j -= 1
    res.append((f'real colourings: {tests} (level, order) tests, {fails} failures, least slack {minslack}', fails == 0 and tests > 0))
    allok = True
    for msg, okk in res:
        print(('PASS ' if okk else 'FAIL ') + msg); allok &= okk
    print('ALL CONTROLS PASSED' if allok else 'SOME CONTROLS FAILED')
    return allok

if __name__ == '__main__':
    a = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, 'certificates', 'unified', 'chain_final.json')
    b = sys.argv[2] if len(sys.argv) > 2 else os.path.join(HERE, 'certificates', 'unified', 'chain_noflag.json')
    sys.exit(0 if main(a, b) else 1)
