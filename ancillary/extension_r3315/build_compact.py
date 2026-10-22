"""Build the full matrix from a compact description (inverse of extract_compact.py).  usage: build_compact.py desc.json out.txt"""
import sys, json
d = json.load(open(sys.argv[1])); n = d['n0']; V = d['anchors']; others = d['others_to_anchors']; X = d['X']
D1, D2 = set(d['D1_red']), set(d['D2_blue'])
def col(i, j):
    t = min((j - i) % n, (i - j) % n)
    return '0' if t in D1 else '1' if t in D2 else '2'
N = n + len(V) + len(others)
M = [['0'] * N for _ in range(N)]
for i in range(n):
    for j in range(n):
        if i != j: M[i][j] = col(i, j)
for k, v in enumerate(V):
    x = n + k
    for h in range(n):
        c = '2' if h == v else M[v][h]
        M[x][h] = M[h][x] = c
for k, s in enumerate(others):
    x = n + len(V) + k
    for h in range(n):
        M[x][h] = M[h][x] = '2'
    for v, c in zip(V, s):
        M[x][v] = M[v][x] = {'r': '0', 'b': '1', 'g': '2'}[c]
for a in range(N - n):
    for b in range(N - n):
        if a != b: M[n + a][n + b] = {'r': '0', 'b': '1', 'g': '2'}[X[a][b]]
with open(sys.argv[2], 'w') as f:
    for row in M: f.write(''.join(row) + '\n')
