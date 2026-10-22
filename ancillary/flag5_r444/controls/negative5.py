"""Negative controls for checkers/check5.py: every perturbed certificate below must be REJECTED.

usage: python3 negative5.py CERT.txt [--r344=K] [--extra-n=N ...]
(the perturbed copies are checked in memory; nothing is written)
 (a) one 'up' cap with q decreased by 1                       -> cap constant assertion
 (b) one 'low' cap with q increased by 1 (if any 'low' cap)   -> lower constant assertion
 (c) one square multiplier negated                            -> lam >= 0 assertion
 (d) every star coefficient + 1e-5 (adds 1e-5 to F everywhere) -> some orbit average of F > 0
 (e) every star coefficient - 1e-5 (subtracts 1e-5 from J)     -> some J(d) <= 0
 (f) all squares removed                                       -> some orbit average of F > 0
 (g) the certificate reused at each --extra-n (n where the relaxation is not decided)
 (h) one 'eloc' up square with q decreased by 1 (if any)       -> eloc cap assertion
 (i) one 'eloc' low square with q increased by 1 (if any)      -> eloc lower constant assertion
"""
import sys, os, copy
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'checkers'))
import check5

args = sys.argv[1:]
extra = [int(a.split('=')[1]) for a in args if a.startswith('--extra-n=')]
for a in [a for a in args if a.startswith('--r344=')]:
    check5.R344 = int(a.split('=')[1]); check5.DMAX = check5.R344 - 1
path = [a for a in args if not a.startswith('--')][0]
cert = check5.load_text(path)


def run(name, c):
    try:
        ok = check5.check(c, label='control ' + name)
        verdict = 'accepted (CONTROL FAILED)' if ok else 'rejected'
    except AssertionError as e:
        ok = False; verdict = f'rejected by assertion: {str(e)[:80]}'
    print(f'control {name}: {verdict}', flush=True)
    return not ok


res = []
for tag, kind, dq in [('h_eloc_up_q_minus_1', 'up', -1), ('i_eloc_low_q_plus_1', 'low', +1)]:
    ids = [i for i, sq in enumerate(cert['squares']) if sq[0] == 'eloc' and sq[3][0] == kind]
    if ids:
        c = copy.deepcopy(cert); sq = list(c['squares'][ids[0]]); k, b, cc, q = sq[3]
        sq[3] = (k, b, cc, q + dq); c['squares'][ids[0]] = tuple(sq)
        res.append(run(tag, c))
c = copy.deepcopy(cert)
i = next(i for i, cp in enumerate(c['caps']) if cp[0] == 'up')
k, p4, kap, q, mu = c['caps'][i]; c['caps'][i] = (k, p4, kap, q - 1, mu)
res.append(run('a_up_q_minus_1', c))
lows = [i for i, cp in enumerate(cert['caps']) if cp[0] == 'low']
if lows:
    c = copy.deepcopy(cert); i = lows[0]
    k, p4, kap, q, mu = c['caps'][i]; c['caps'][i] = (k, p4, kap, q + 1, mu)
    res.append(run('b_low_q_plus_1', c))
c = copy.deepcopy(cert)
sq = list(c['squares'][0]); sq[2] = -Fr(sq[2]); c['squares'][0] = tuple(sq)
res.append(run('c_lam_negated', c))
c = copy.deepcopy(cert); c['star'] = {k: Fr(v) + Fr(1, 10 ** 5) for k, v in c['star'].items()}
res.append(run('d_star_plus_1e-5', c))
c = copy.deepcopy(cert); c['star'] = {k: Fr(v) - Fr(1, 10 ** 5) for k, v in c['star'].items()}
res.append(run('e_star_minus_1e-5', c))
c = copy.deepcopy(cert); c['squares'] = []
res.append(run('f_no_squares', c))
for m in extra:
    c = copy.deepcopy(cert); c['n'] = m
    res.append(run(f'g_reused_at_{m}', c))
print('ALL CONTROLS REJECTED' if all(res) else 'SOME CONTROL ACCEPTED')
sys.exit(0 if all(res) else 1)
