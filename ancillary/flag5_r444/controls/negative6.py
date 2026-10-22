"""Negative controls for checkers/check6.py on a certificate: each perturbed copy must be rejected.
 (a) an 'up' cap with q - 1, (b) an 'eloc' up square with q - 1, (c) all star coefficients + 1e-5,
 (d) the certificate reused at n - 1 with the n-dependent lower constants shifted (boundary control).
usage: python3 negative6.py CERT.txt   (needs numpy, as check6.py; the perturbed copies are checked in memory)"""
import sys, os, copy
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'checkers'))
import check6
cert = check6.load_text(sys.argv[1]); res = []
def run(tag, c):
    try: ok = check6.check(c, label='control ' + tag); v = 'accepted (CONTROL FAILED)' if ok else 'rejected'
    except AssertionError as e: ok = False; v = 'rejected by assertion ' + str(e)[:60]
    print('control', tag, ':', v, flush=True); res.append(not ok)
c = copy.deepcopy(cert); i = next(i for i, x in enumerate(c['caps']) if x[0] == 'up')
k, p4, kap, q, mu = c['caps'][i]; c['caps'][i] = (k, p4, kap, q - 1, mu); run('a_cap_q_minus_1', c)
c = copy.deepcopy(cert); i = next(i for i, x in enumerate(c['squares']) if x[0] == 'eloc' and x[3][0] == 'up')
s = list(c['squares'][i]); kk, b, cc, q = s[3]; s[3] = (kk, b, cc, q - 1); c['squares'][i] = tuple(s); run('b_eloc_q_minus_1', c)
c = copy.deepcopy(cert); c['star'] = {k: Fr(v) + Fr(1, 10 ** 5) for k, v in c['star'].items()}; run('c_star_plus_1e-5', c)
c = copy.deepcopy(cert); m = cert['n'] - 1; c['n'] = m
c['caps'] = [(k, p4, kap, q - 1 if k == 'low' else q, mu) for k, p4, kap, q, mu in c['caps']]
c['squares'] = [(s[0], s[1], s[2], (s[3][0], s[3][1], s[3][2], s[3][3] - 1)) if s[0] == 'eloc' and s[3][0] == 'low' else s
                for s in c['squares']]
run(f'd_reuse_at_{m}', c)
print('ALL CONTROLS REJECTED' if all(res) else 'SOME CONTROL ACCEPTED')
sys.exit(0 if all(res) else 1)
