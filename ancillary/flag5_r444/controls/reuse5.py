"""Boundary control: reuse a certificate at a smaller m, with every n-dependent lower constant (the 'low' caps and
'eloc' low squares, q <= m-1-2*76 - known) lowered by n - m so that it stays valid at m.  At an m where the
relaxation is undecided the checker must reject the certificate on (B) or (C).
usage: python3 reuse5.py CERT.txt m"""
import sys, os, copy
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'checkers'))
import check5
cert = check5.load_text(sys.argv[1]); m = int(sys.argv[2]); dn = cert['n'] - m
c = copy.deepcopy(cert); c['n'] = m
c['caps'] = [(k, p4, kap, q - dn if k == 'low' else q, mu) for k, p4, kap, q, mu in c['caps']]
sq = []
for s in c['squares']:
    if s[0] == 'eloc' and s[3][0] == 'low':
        k, b, cc, q = s[3]; s = (s[0], s[1], s[2], (k, b, cc, q - dn))
    sq.append(s)
c['squares'] = sq
ok = check5.check(c, label=f'reuse at {m}')
print('control reuse at', m, ':', 'accepted (CONTROL FAILED)' if ok else 'rejected')
sys.exit(1 if ok else 0)
