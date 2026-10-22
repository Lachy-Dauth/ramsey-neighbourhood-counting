"""Negative controls for a (3,3,k;n) witness: usage controls.py KCHECK witness.txt k outprefix
(KCHECK: the compiled kcheck.cpp; the perturbed matrices are written to outprefix_*.txt)
1. kcheck -max 2 must report clique number k-1 (and print a (k-1)-set W).
2. red-triangle control: recolour one edge to close a red path a-b-c; kcheck must find a red K3.
3. green K_k control: a vertex u green to all but one member of W; recolour that edge green; kcheck must find a green K_k.
"""
import sys, subprocess, re
KC, fn, k, pre = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
A = [list(l.strip()) for l in open(fn) if l.strip()]; n = len(A)
def run(args):
    r = subprocess.run(args, capture_output=True, text=True); return r.stdout
def write(B, out):
    with open(out, 'w') as f:
        for row in B: f.write(''.join(row) + '\n')
out = run([KC, fn, '-max', '2']); print(out.strip())
W = [int(x) for x in out.split('witness:')[1].split()]
w = int(re.search(r'clique_number=(\d+)', out).group(1))
print('control 1: clique number', w, 'expected', k - 1, 'PASS' if w == k - 1 else 'FAIL')
# control 2
done = False
for a in range(n):
    reds = [b for b in range(n) if b != a and A[a][b] == '0']
    for b in reds:
        for c in reds:
            if b < c and A[b][c] != '0':
                B = [r[:] for r in A]; B[b][c] = B[c][b] = '0'; out2 = pre + '_redK3.txt'; write(B, out2)
                o = run([KC, out2, '3', str(n), str(n)]).strip().splitlines()[0]
                print('control 2: edge', b, c, 'recoloured red;', o, 'PASS' if 'clique_found=true' in o else 'FAIL'); done = True; break
        if done: break
    if done: break
# control 3
Ws = set(W); done = False
for u in range(n):
    if u in Ws: continue
    non = [x for x in W if A[u][x] != '2']
    if len(non) == 1:
        x = non[0]; B = [r[:] for r in A]; B[u][x] = B[x][u] = '2'; out3 = pre + '_greenK%d.txt' % k; write(B, out3)
        o = run([KC, out3, str(n), str(n), str(k)]).strip().splitlines()[-1]
        print('control 3: u', u, 'edge', u, x, 'recoloured green;', o, 'PASS' if 'clique_found=true' in o else 'FAIL'); done = True; break
if not done: print('control 3: no vertex green to all but one member of W')
