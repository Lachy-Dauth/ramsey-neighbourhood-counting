"""Check the expansion used for 'eloc' squares: for a random colouring of K_n (n = 9) and each ordered pair (x0,x1),
the average over distinct x2,x3,x4 of EQ and H equals (v0 + A)^2 and |S| (v0 + A)^2 exactly."""
import random
from fractions import Fraction as Fr
from itertools import permutations
random.seed(5); n = 9; N = n - 2
col = {}
for i in range(n):
    for j in range(i + 1, n): col[(i, j)] = col[(j, i)] = random.randrange(3)
v = [Fr(random.randint(-9, 9)) for _ in range(10)]
bad = 0
for b, c in [(0, None), (1, 2), (2, 2), (None, 1)]:
    for x0, x1 in permutations(range(n), 2):
        others = [w for w in range(n) if w not in (x0, x1)]
        u = {w: v[1 + 3 * col[(x0, w)] + col[(x1, w)]] for w in others}
        s = {w: int((b is None or col[(x0, w)] == b) and (c is None or col[(x1, w)] == c)) for w in others}
        A = sum(u.values()) / Fr(N); S = sum(s.values())
        eq = h = Fr(0); cnt = 0
        for x2, x3, x4 in permutations(others, 3):
            u2, u3, u4, s2 = u[x2], u[x3], u[x4], s[x2]
            eq += v[0] ** 2 + 2 * v[0] * u2 + u2 * u2 / N + Fr(N - 1, N) * u2 * u3
            h += (N * v[0] ** 2 * s2 + 2 * v[0] * (s2 * u2 + (N - 1) * s2 * u3)
                  + (s2 * u2 * u2 + 2 * (N - 1) * s2 * u2 * u3 + (N - 1) * s2 * u3 * u3 + (N - 1) * (N - 2) * s2 * u3 * u4) / Fr(N))
            cnt += 1
        bad += (eq / cnt != (v[0] + A) ** 2) + (h / cnt != S * (v[0] + A) ** 2)
print('mismatches:', bad)
import sys; sys.exit(0 if bad == 0 else 1)
