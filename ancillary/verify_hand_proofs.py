"""Exact check of every numerical step in Sections 4 and 6 of the paper.

Standard library only. Each check mirrors one displayed statement; the
mathematical justification of the inequalities themselves is in the paper.
Run: python3 verify_hand_proofs.py
"""
from fractions import Fraction as Fr
from itertools import product
from math import ceil, comb

checks = 0


def ok(cond, what):
    global checks
    assert cond, what
    checks += 1


def F(n, k, U, h):  # Lemma 3.2 without the bracket
    return 3 * h * h + (U + 5 - 3 * n - 3 * k) * h + (n - U - 1) * (n - 1)


# ---------------- Theorem 4.1: R(3,3,6) <= 88 ----------------
for h in range(0, 35):
    x = 34 - h
    ok(F(88, 6, 30, h) == 29 + 43 * x + 3 * x * x, "F88 closed form")
    ok(F(88, 6, 30, h) > 0, "F88 positive")
ok(F(87, 6, 30, 34) == -12 and F(87, 6, 30, 34) + 6 == -6, "the argument stops at 88")
ok(86 - 34 <= 56, "h=34 admissible at n=87")

# ---------------- Lemma 4.2: chords, q = floor(smaller root) ----------------
chord = {79: 26, 80: 27, 81: 28, 82: 29, 83: 30, 84: 30, 85: 31, 86: 32, 87: 33}
expect = {79: (61, 1638, 1061), 80: (58, 1603, 1106), 81: (55, 1564, 1152), 82: (52, 1521, 1200),
          83: (49, 1474, 1249), 84: (52, 1609, 1300), 85: (49, 1560, 1354), 86: (46, 1507, 1409),
          87: (43, 1450, 1467)}
m6c = {}
for z, q in chord.items():
    ok(F(z, 6, 30, q) > 0 >= F(z, 6, 30, q + 1) or F(z, 6, 30, q) >= 0 > F(z, 6, 30, q + 1), "q = floor(r)")
    beta = 3 * z - 20 - 6 * q
    alpha = (z - 31) * (z - 1) - 3 * q * (q + 1)
    for h in range(-5, z + 5):
        ok(F(z, 6, 30, h) == alpha - beta * h + 3 * (h - q) * (h - q - 1), "chord identity")
        ok((h - q) * (h - q - 1) >= 0, "consecutive integers")
    m6c[z] = ceil(Fr(z * alpha, 2 * beta))
    ok((beta, alpha, m6c[z]) == expect[z], f"chord table z={z}")

# ---------------- Theorem 4.3: R(3,3,7) <= 129 ----------------
ok([F(129, 7, 57, h) for h in range(41, 45)] == [-55, -152, -243, -328], "F at 129 without m6 (remark)")
row = {h: h * (2 * h - 147) + 2 * m6c[128 - h] for h in range(41, 45)}
ok(row == {41: 269, 42: 172, 43: 85, 44: 4}, "table of Theorem 4.3")
ok(2 * 23 + 91 - 1 == 136 and 2 * 23 + 88 - 1 == 133, "comparison values")

# ---------------- Lemma 4.4: m7 ----------------
g = {h: h * (2 * h - 142) + 2 * m6c[123 - h] for h in range(36, 45)}
ok(list(g.values()) == [414, 302, 200, 104, 18, -60, -132, -196, -254], "g table")
ok([g[h] - (3138 - 78 * h) for h in g] == [84, 50, 26, 8, 0, 0, 6, 20, 40], "supporting line gaps")
ok(all(g[h] >= 3138 - 78 * h for h in g), "line below g")
m7 = {124: ceil(Fr(124 * 3138, 156))}
for z in range(125, 129):
    m7[z] = m7[z - 1] + (z - 88)
ok(m7 == {124: 2495, 125: 2532, 126: 2570, 127: 2609, 128: 2649}, "m7 values")

# ---------------- Theorem 4.5: R(3,3,8) <= 179 ----------------
ok([h * (2 * h - 200) + 2 * m7[178 - h] for h in range(50, 55)] == [298, 220, 148, 82, 22], "table of Theorem 4.6")

# ---------------- Recurrence (1) with the parity refinement [DS1 6.1(a)] ----------------
def P(terms):
    """Sum of terms minus 1, reduced by 1 if that is even and some term is even."""
    s = sum(terms) - 1
    return s - 1 if (s % 2 == 0 and any(t % 2 == 0 for t in terms)) else s


ok(P([18, 18, 57]) == 91, "R(3,3,6) <= 91 from parity")
R3 = {7: 23, 8: 28, 9: 36, 10: 41, 11: 50, 12: 59, 13: 68, 14: 77, 15: 87}
new = {6: 88, 7: 129, 8: 179, 9: 247, 10: 315, 11: 407, 12: 512, 13: 628, 14: 756, 15: 901}
rec, prev = {}, 91
for k in range(7, 16):
    prev = P([R3[k], R3[k], prev])
    rec[k] = prev
ok((rec[7], rec[8]) == (136, 191), "136, 191")
ok([rec[k] for k in range(9, 16)] == [261, 342, 441, 558, 693, 846, 1019], "Table 4 row 2")
ok([P([R3[k], R3[k], new[k - 1]]) for k in range(9, 16)] == [249, 328, 413, 524, 647, 781, 929], "Table 4 row 3")
ok(P([23, 23, 88]) == 133, "133")


# ---------------- Lemma 6.1 on all 27 coloured triangles ----------------
def W(d, w):
    return sum(w[i] * comb(d[i], 2) for i in range(3)) + w[3] * d[0] * d[1] + w[4] * d[0] * d[2] + w[5] * d[1] * d[2]


PAIR = {(0, 1): 3, (0, 2): 4, (1, 2): 5}


def triangle_coefficient(edges, w):
    hist = [edges.count(i) for i in range(3)]
    if 3 in hist:
        return 3 * w[hist.index(3)]
    if 2 in hist:
        i, j = hist.index(2), hist.index(1)
        return w[i] + 2 * w[PAIR[tuple(sorted((i, j)))]]
    return w[3] + w[4] + w[5]


def check_weighted_identity(w):
    for edges in product(range(3), repeat=3):  # colours of 01, 02, 12
        deg = [[0] * 3 for _ in range(3)]
        for (u, v), c in zip([(0, 1), (0, 2), (1, 2)], edges):
            deg[u][c] += 1
            deg[v][c] += 1
        ok(sum(W(deg[v], w) for v in range(3)) == triangle_coefficient(list(edges), w), "Lemma 6.1")


# ---------------- Theorem 6.2: R(3,4,5) <= 155 ----------------
w345 = (78, 58, 78, -29, -39, 68)
check_weighted_identity(w345)
coef = {}
for pattern, edges in {"RRB": (0, 0, 1), "RRG": (0, 0, 2), "BBR": (1, 1, 0), "BBG": (1, 1, 2), "GGR": (2, 2, 0),
                       "GGB": (2, 2, 1), "BBB": (1, 1, 1), "GGG": (2, 2, 2), "RGB": (0, 1, 2)}.items():
    coef[pattern] = triangle_coefficient(list(edges), w345)
ok(coef == {"RRB": 20, "RRG": 0, "BBR": 0, "BBG": 194, "GGR": 0, "GGB": 214, "BBB": 174, "GGG": 234, "RGB": 0},
   "surviving coefficients")
ok(Fr(20 * 13, 2) == 130 and Fr(194 * 29, 2) + Fr(58 * 13, 2) == 3190 and Fr(214 * 29, 2) + Fr(78 * 29, 2) == 4234,
   "combined caps")
for r in range(0, 25):
    for b in range(0, 57):
        gg = 154 - r - b
        x, y = 24 - r, 56 - b
        val = W((r, b, gg), w345) - 130 * r - 3190 * b - 4234 * gg
        ok(val == 2 + 7178 * x + 117 * x * x + 6 * y + 20 * x * y, "R345 polynomial")
        ok(val >= 2, "R345 positive")
ok(155 * 1102 == 170810 and 170810 % 3 == 2 and 76 * 29 == 2 * 1102, "divisibility aside")
for al, ga in [(29, 39), (3, 4), (1, 2), (5, 7)]:
    w = (2 * ga, 2 * al, 2 * ga, -al, -ga, al + ga)
    for r in range(0, 25):
        for b in range(0, 57):
            gg, x, y = 154 - r - b, 24 - r, 56 - b
            val = W((r, b, gg), w) - 13 * (ga - al) * r - (71 * al + 29 * ga) * b - (29 * al + 87 * ga) * gg
            ok(val == (70 * al - 52 * ga) + (70 * al + 132 * ga) * x + 3 * ga * x * x + (47 * ga - 63 * al) * y
               + 2 * (ga - al) * x * y, "R345 general form")
ok(Fr(35, 26) - Fr(63, 47) == Fr(7, 1222) and Fr(35, 26) - Fr(4, 3) == Fr(1, 78), "interval widths")
ok(min((Fr(p, q) for q in range(1, 30) for p in range(q, 2 * q) if Fr(63, 47) <= Fr(p, q) < Fr(35, 26)),
       key=lambda f: f.denominator) == Fr(39, 29), "39/29 has the least denominator")
phi34 = lambda x, y: 2 + 738 * x + 12 * x * x - y + 2 * x * y
ok(phi34(0, 4) == -2 and [(x, y) for x in range(3) for y in range(3 - x) if phi34(x, y) <= 0] == [(0, 2)], "earlier weights")

# ---------------- Theorems 6.3, 6.4 ----------------
wL = (-2, 4, 4, 1, 1, -2)
check_weighted_identity(wL)
worst = None
for r in range(0, 41):  # published R(4,6) <= 41; no cap on g is used
    for b in range(0, 88):
        gg = 275 - r - b
        if gg < 0:
            continue
        x, y = 40 - r, 87 - b
        val = W((r, b, gg), wL) - 85 * b - 224 * gg
        ok(val == 17 + 76 * x + 227 * y + 6 * x * y + 6 * y * y, "R346 polynomial")
        worst = val if worst is None else min(worst, val)
        if r <= 39:
            ok(val >= 93, "R346 margin with unpublished R(4,6) <= 40")
ok(W((40, 87, 148), wL) == 40564 and 85 * 87 + 224 * 148 == 40547, "R346 base point")
ok(W((39, 87, 148), wL) - 85 * 87 - 224 * 148 == -140, "275 not excluded")
ok(worst == 17, "R346 margin with published R(4,6) <= 41")
for r in range(0, 46):
    for b in range(0, 155):
        gg = 345 - r - b
        if not (0 <= gg <= 154):
            continue
        x, y = 154 - b, 154 - gg
        val = W((r, b, gg), wL) - 184 * b - 184 * gg
        ok(val == 208 + 76 * x + 76 * y - 6 * x * y and val >= 208, "R355")
ok(W((36, 154, 154), wL) - 184 * 308 == -28, "345 not excluded")
ok((P([40, 91, 157]), P([46, 157, 157]), P([40, 88, 155]), P([46, 155, 155])) == (287, 359, 281, 355), "comparisons")
ok((P([58, 136, 287]), P([79, 191, P([58, 136, 287])]), P([85, 287, 359])) == (479, 748, 730), "Table 1 daggers")
ok(P([41, 88, 155]) == 283, "283 with the published R(4,6) <= 41")
pb = P([41, 91, 157])
ok((pb, P([61, 136, pb]), P([84, 191, P([61, 136, pb])]), P([87, pb, P([46, 157, 157])])) == (288, 483, 757, 733),
   "published-only benchmarks (Table 1 caption)")

# ---------------- Proposition 6.5: the hand reductions of the margins ----------------
w2 = (2, 2, 2, 2, -1, -1)
check_weighted_identity(w2)
def profiles(n, D):
    return [(r, b, n - 1 - r - b) for r in range(D[0] + 1) for b in range(D[1] + 1) if 0 <= n - 1 - r - b <= D[2]]
for n, D, C, C33, lin, mn, att in [(456, (57, 128, 275), 22, 154, (1277, 133684), 114, (57, 128, 270)),
                                    (700, (78, 178, 455), 27, 275, (1903, 290871), 311, (78, 178, 443))]:
    vals = {}
    for (r, b, gg) in profiles(n, D):
        s_ = r + b
        val = W((r, b, gg), w2) - 3 * C * r - 4 * C * b - C33 * gg
        ok(val == 3 * s_ * s_ - lin[0] * s_ + lin[1] + C * (D[1] - b), f"reduction at n={n}")
        vals[(r, b, gg)] = val
    ok(min(vals.values()) == mn and vals[att] == mn, f"floor-free minimum at n={n}")
for (r, b, gg) in profiles(683, (84, 275, 345)):
    x, y = 275 - b, 345 - gg
    ok(W((r, b, gg), wL) - 291 * b - 443 * gg == 108 + 318 * x + 50 * y - 6 * x * y, "reduction at n=683")

print(f"all {checks} checks passed")
