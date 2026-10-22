#!/usr/bin/env python3
"""Positive controls of check_flag5_mix.py on the (3,3,3;16) colouring (cubic residues of GF(16)*), where every
profile is (5,5,5) = (D_0, D_1, D_2), so the 'low' rows have positive constants Lo_c = 5 and are tight; also on
a 13-vertex subset (irregular).  Colour of {x,y} = (log_g (x XOR y)) mod 3, g a root of z^4 + z + 1."""
import os, sys, random
here = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, here)
import controls_flag5 as CF
log = {}; x = 1
for k in range(15):
    log[x] = k
    x <<= 1
    if x & 16:
        x ^= 0b10011
colf = lambda u, v: log[u ^ v] % 3
rnd = random.Random(9)
ok = CF.positive((3, 3, 3), 16, colf, '(3,3,3;16) cubic-residue colouring', rnd, 60)
keep = sorted(rnd.sample(range(16), 13))
ok &= CF.positive((3, 3, 3), 13, lambda u, v: colf(keep[u], keep[v]), '(3,3,3;16) on 13 random vertices', rnd, 60)
print('ALL CONTROLS PASSED' if ok else 'SOME CONTROL FAILED')
sys.exit(0 if ok else 1)
