#!/usr/bin/env python3
"""Negative controls for five-vertex certificates (check_r33k5.py), in the state of the unified chain.

  python3 controls5.py chain.json cert5.json [more cert5.json ...]

The chain is checked up to level k-1 of each certificate (so that its rec values are justified), then:
  1. the certificate is accepted;
  2. h* raised by 10^-9 is rejected, and m raised by one is rejected (density certificates);
  3. one cap constant changed by one is rejected (constant mismatch);
  4. one rec value raised above the verified table is rejected;
  5. a row multiplier lowered by 1%, and a square dropped (8 random ones of each): the numbers rejected are reported
     (a row or square may be slack, so not every perturbation need fail);
  6. all star coefficients raised by 10^-6 is rejected (Phi then exceeds 0 on some orbit).
"""
import copy, io, json, sys, contextlib
from fractions import Fraction as Fr
import check_unified as U
import check_r33k as C
import check_r33k5 as F

def run(cert):
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        try: ok = F.check(cert, verbose=False)
        except (AssertionError, KeyError, ValueError): ok = False
    return ok

def main(chain, paths):
    allok = True
    for path in paths:
        cert = json.load(open(path)); k = cert['k']
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf): U.main(chain, verbose=False, kmax=k - 1)
        C.R33[k] = min(C.R33[k], 10 ** 9)
        res = []
        res.append(('accepted', run(cert)))
        if cert.get('type') == 'density':
            d = copy.deepcopy(cert); d['hstar'] = str(Fr(d['hstar']) + Fr(1, 10 ** 9)); res.append(('h* + 1e-9 rejected', not run(d)))
            d = copy.deepcopy(cert); d['m'] += 1; res.append(('m + 1 rejected', not run(d)))
        i = next((i for i, r in enumerate(cert['rows']) if r['kind'] in ('up', 'low')), None)
        if i is not None:
            d = copy.deepcopy(cert); d['rows'][i]['q'] += (-1 if d['rows'][i]['kind'] == 'up' else 1); res.append(('cap constant strengthened by one (unjustified) rejected', not run(d)))
        i = next((i for i, r in enumerate(cert['rows']) if r['kind'] == 'rec'), None)
        if i is not None:
            d = copy.deepcopy(cert); g = max(d['rows'][i]['m'], key=lambda x: int(x)); d['rows'][i]['m'][g] = int(d['rows'][i]['m'][g]) + 10 ** 6
            res.append(('rec value raised rejected', not run(d)))
        import random
        rng = random.Random(0)
        sr = sorted(rng.sample(range(len(cert['rows'])), min(8, len(cert['rows']))))
        rej = 0
        for i in sr:
            d = copy.deepcopy(cert); d['rows'][i]['mu'] = str(Fr(d['rows'][i]['mu']) * Fr(99, 100)); rej += not run(d)
        res.append((f'row multiplier - 1% (8 random rows): {rej}/{len(sr)} rejected (reported)', True))
        ss = sorted(rng.sample(range(len(cert['squares'])), min(8, len(cert['squares']))))
        rej = 0
        for i in ss:
            d = copy.deepcopy(cert); del d['squares'][i]; rej += not run(d)
        res.append((f'square dropped (8 random squares): {rej}/{len(ss)} rejected (reported)', True))
        d = copy.deepcopy(cert); import itertools
        d['star'] = {''.join(t): str(Fr(d['star'].get(''.join(t), 0)) + Fr(1, 10 ** 6)) for t in itertools.product('RBG', repeat=4)}
        res.append(('star coefficients + 1e-6 rejected', not run(d)))
        print(path)
        for msg, ok in res:
            print(('  PASS ' if ok else '  FAIL ') + msg); allok &= ok
    print('ALL CONTROLS5 PASSED' if allok else 'SOME CONTROLS5 FAILED')
    return allok

if __name__ == '__main__':
    sys.exit(0 if main(sys.argv[1], sys.argv[2:]) else 1)
