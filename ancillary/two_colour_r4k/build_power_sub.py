#!/usr/bin/env python3
"""Independent builder: power-residue graph minus a vertex set.
  build_power_sub.py p e delfile out.txt
Vertices 0..p-1 (p prime), x ~ y iff x - y is a nonzero e-th power mod p (requires -1 to be an
e-th power so the relation is symmetric).  Vertices listed in delfile (whitespace separated; a
leading 'HIT k:' or similar token without digits-only form is ignored) are deleted; remaining
vertices keep their natural order.  Writes n and the adjacency matrix rows."""
import sys
p, e = int(sys.argv[1]), int(sys.argv[2])
for d in range(2, int(p ** 0.5) + 1):
    assert p % d, "p not prime"
R = set(pow(x, e, p) for x in range(1, p))
assert (p - 1) in R, "-1 is not an e-th power: graph would not be undirected"
D = set()
for tok in open(sys.argv[3]).read().split():
    if tok.isdigit():
        D.add(int(tok))
assert all(0 <= v < p for v in D)
keep = [v for v in range(p) if v not in D]
with open(sys.argv[4], 'w') as f:
    f.write(f"{len(keep)}\n")
    for u in keep:
        f.write(''.join('1' if (u != v and ((u - v) % p) in R) else '0' for v in keep) + "\n")
print(f"p={p} e={e} |R|={len(R)} deleted={len(D)} n={len(keep)}")
