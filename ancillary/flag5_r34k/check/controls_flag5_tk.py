#!/usr/bin/env python3
"""Positive controls of check_flag5_mix.py for t = (3,4,6), (3,4,7), (3,4,8), (3,5,6): a (3,4,5)-colouring avoids each
of these, so random 17-vertex subsets of the (3,4,5;30) circulant (data/circ_345.json) are used with the checker's
term functions for each t (caps from the checker's own tables)."""
import json, os, sys, random
here = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, here)
import controls_flag5 as CF
rnd = random.Random(13)
colv = json.load(open(os.path.join(here, '..', 'data', 'circ_345.json')))['30']
colf = lambda u, v: colv[(v - u) % 30 - 1]
ok = True
for t in [(3, 4, 6), (3, 4, 7), (3, 4, 8), (3, 5, 6)]:
    keep = sorted(rnd.sample(range(30), 17))
    ok &= CF.positive(t, 17, lambda u, v, keep=keep: colf(keep[u], keep[v]), f'(3,4,5;30) circulant on 17 vertices as {t}', rnd, 40)
print('ALL CONTROLS PASSED' if ok else 'SOME CONTROL FAILED')
sys.exit(0 if ok else 1)
