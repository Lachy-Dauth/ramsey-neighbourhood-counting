#!/usr/bin/env python3
"""Positive controls of check_flag5_mix.py for t = (4,4,4) (colour group S3), on random 17-vertex subsets of
the (4,4,4;30) circulant colouring in data/circ_444.json."""
import json, os, sys, random
here = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, here)
import controls_flag5 as CF
rnd = random.Random(5)
circ = json.load(open(os.path.join(here, '..', 'data', 'circ_444.json'))); colv = circ['30']
colf = lambda u, v: colv[(v - u) % 30 - 1]
ok = True
for trial in range(2):
    keep = sorted(rnd.sample(range(30), 17))
    colg = lambda u, v, keep=keep: colf(keep[u], keep[v])
    ok &= CF.positive((4, 4, 4), 17, colg, 'circulant (4,4,4;30) on 17 random vertices', rnd, 60)
print('ALL CONTROLS PASSED' if ok else 'SOME CONTROL FAILED')
sys.exit(0 if ok else 1)
