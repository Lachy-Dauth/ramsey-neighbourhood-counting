"""Certificate check for a colouring F = H + X (H = first n0 vertices), written from the definitions.

Claim checked: F has no green K_k, given that the green clique number of H is at most q.
Argument: a green clique of F is S + T with S a green clique of X and T a green clique of H inside
C(S) = H minus the union of A_x (x in S), A_x = red or blue neighbours of x in H.  Call w in H a certifier of S if
w and all red and blue neighbours of w in H lie in that union.  If W' is a set of certifiers that is a green clique
of H, every green clique T in C(S) is green to all of W' and disjoint from it, so |T| <= q - |W'|.
Hence it suffices that |S| + q - omega(W(S)) <= k - 1 for every green clique S of X (S empty included), where
W(S) is the set of certifiers and omega is the green clique number of H restricted to W(S).
Also checks red and blue triangle-freeness of F directly.
usage: certcheck.py F.txt n0 q k
"""
import sys, itertools

fn, n0, q, k = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
A = [l.strip() for l in open(fn) if l.strip()]
N = len(A)
assert all(len(r) == N for r in A)
for i in range(N):
    for j in range(N):
        if i != j:
            assert A[i][j] in '012' and A[i][j] == A[j][i]
# red / blue triangles, directly
nbr = [[set(j for j in range(N) if j != i and A[i][j] == c) for i in range(N)] for c in '012']
tri = 0
for c in (0, 1):
    for i in range(N):
        for j in nbr[c][i]:
            if j > i and (nbr[c][i] & nbr[c][j]):
                tri += 1
print('red/blue triangles:', tri)
H = range(n0)
X = list(range(n0, N))
nonG_H = [set(h for h in H if h != v and A[v][h] in '01') for v in range(N)]   # red/blue nbrs in H
closedNB = [nonG_H[w] | {w} for w in H]


def green_omega(W):
    """exact green clique number of H restricted to W (small sets)"""
    W = sorted(W); best = 0

    def rec(cl, cand):
        nonlocal best
        if len(cl) > best:
            best = len(cl)
        for i, v in enumerate(cand):
            if len(cl) + len(cand) - i <= best:
                return
            rec(cl + [v], [u for u in cand[i + 1:] if A[v][u] == '2'])
    rec([], W)
    return best


worst = None; nS = 0; ok = True; hist = {}
def recS(S, cand):
    global worst, nS, ok
    nS += 1
    U = set().union(*[nonG_H[x] for x in S]) if S else set()
    W = [w for w in H if closedNB[w] <= U] if S else []
    wW = green_omega(W)
    val = len(S) + q - wW
    key = (len(S), wW); hist[key] = hist.get(key, 0) + 1
    if val > k - 1:
        ok = False
        print('FAIL: S =', S, 'certifiers', len(W), 'omega(W) =', wW, 'bound', val)
    if worst is None or val > worst[0]:
        worst = (val, list(S), wW)
    for i, x in enumerate(cand):
        recS(S + [x], [y for y in cand[i + 1:] if A[x][y] == '2'])
recS([], X)
print('green cliques S of X examined:', nS, ' (|S|, omega(certifiers)) histogram:', dict(sorted(hist.items())))
print('max over S of |S| + q - omega(W(S)) =', worst[0], 'at S =', worst[1])
if ok and tri == 0:
    print('RESULT: PASS (no red/blue K3; green clique number <= %d given omega_green(H) <= %d)' % (k - 1, q))
else:
    print('RESULT: FAIL (%s)' % '; '.join(([] if tri == 0 else ['%d red/blue triangles' % tri]) +
          ([] if ok else ['some green clique S of X has |S| + q - omega(W(S)) > %d' % (k - 1)])))
