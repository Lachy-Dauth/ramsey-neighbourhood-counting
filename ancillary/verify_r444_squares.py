"""Exact check of the multi-square certificates for R(4,4,4) <= n (Section 7).  Standard library only.

Certificates are in r444_squares.json.  Setting (Section 7): c is a (4,4,4;n)-colouring, (x0,x1,x2,x3) a
uniformly random ordered quadruple of distinct vertices, sigma an independent uniform bijection from the
colours to the labels R, B, G, and c_ij the label of x_i x_j.  The law of (c_ij) is invariant under
S4 x S3, so for any function f of the labelled K4, E[f] = E[Sym f], where Sym averages over the group.

A certificate gives rationals cs, ce, ct, cap rows ell_i with multipliers mu_i >= 0, and squares Q_j with
multipliers lam_j >= 0, such that
  (1) Sym F <= 0 on every labelled K4 colouring that is not a monochromatic K4 (which has probability 0),
      where F = cs 1[s] + ce 1[eta] + ct 1[t] - sum_i mu_i ell_i + sum_j lam_j Q_j;
  (2) J(d) = cs s(d) + ce eta(d) + ct t(d) > 0 at every degree profile d (entries <= 76, sum n-1).
Each ell_i <= 0 and each Q_j >= 0 in expectation, so E[cs s + ce eta + ct t] <= 0.  But this expectation
is the average over x0 = v of J(d(v)) > 0, a contradiction.  Here s, eta, t are the events
c01=c02=c03=R;  c01=c02=R, c03=B;  c01=R, c02=B, c03=G.

Cap rows (Lemma 7.2): a pattern tau = (c01, c02, c12) and a condition on x3:
  "deg"  c03 = X            x3 in S = N_X(x0), |S| <= 76;
  "low"  c03 = X            |N_X(x0)| >= n-1-2*76 (a lower bound, row sign reversed);
  "int"  c03 = c01, c13 = Y x3 in S = N_{c01}(x0) cap N_Y(x1), |S| <= 17 if Y = c01, else 29;
and q is the cap less the number of x1, x2 in S.  The row is ell = 1[tau, cond] - (q/(n-3)) 1[tau]
(for "low": (q/(n-3)) 1[tau] - 1[tau, cond]).  The checker recomputes every q from these rules.
Squares: Q = E[1_{c01=R} (v0 + Z/(n-2))^2] >= 0 with Z = sum_{w != x0,x1} a(c(x0 w), c(x1 w)); averaging
over (x2,x3) gives 1_{c01=R}(v0^2 + 2 v0 a2 + a2^2/(n-2) + (n-3)/(n-2) a2 a3), a_j = a(c_0j, c_1j).
Run: python3 verify_r444_squares.py
"""
import json
from fractions import Fraction as Fr
from itertools import permutations, product
from pathlib import Path

L = {"R": 0, "B": 1, "G": 2}
EDGES = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]


def cap_q(kind, tau, x, y, n):
    if kind in ("deg", "low"):
        known = (tau[0] == x) + (tau[1] == x)
        return 76 - known if kind == "deg" else (n - 1 - 2 * 76) - known
    assert kind == "int" and x == tau[0], "intersection rows need x1 in N_x(x0)"
    return (17 if y == x else 29) - int(tau[1] == x and tau[2] == y)


def check(cert):
    n = cert["n"]
    cs, ce, ct = (Fr(cert["lhs"][k]) for k in ("s", "eta", "t"))
    rows = []
    for r in cert["caps"]:
        tau = tuple(L[ch] for ch in r["tau"])
        x = L[r["c03"]]
        y = L[r["c13"]] if r.get("c13") else None
        q = cap_q(r["kind"], tau, x, y, n)
        assert q == r["q"], f"cap constant {r} should be {q}"
        mu = Fr(r["mu"])
        assert mu >= 0
        rows.append((r["kind"], tau, x, y, Fr(q, n - 3), mu))
    squares = []
    for sq in cert["squares"]:
        lam = Fr(sq["lambda"])
        assert lam >= 0
        a = {(L[k[0]], L[k[1]]): Fr(v) for k, v in sq["a"].items()}
        squares.append((Fr(sq["v0"]), a, lam))

    def F(c):
        tau = (c[(0, 1)], c[(0, 2)], c[(1, 2)])
        val = Fr(0)
        if c[(0, 1)] == c[(0, 2)] == c[(0, 3)] == 0:
            val += cs
        if (c[(0, 1)], c[(0, 2)], c[(0, 3)]) == (0, 0, 1):
            val += ce
        if (c[(0, 1)], c[(0, 2)], c[(0, 3)]) == (0, 1, 2):
            val += ct
        for kind, rt, x, y, frac, mu in rows:
            if tau != rt:
                continue
            ev = int(c[(0, 3)] == x and (y is None or c[(1, 3)] == y))
            val -= mu * ((frac - ev) if kind == "low" else (ev - frac))
        if c[(0, 1)] == 0:
            for v0, a, lam in squares:
                a2, a3 = a.get((c[(0, 2)], c[(1, 2)]), 0), a.get((c[(0, 3)], c[(1, 3)]), 0)
                val += lam * (v0 * v0 + 2 * v0 * a2 + Fr(1, n - 2) * a2 * a2 + Fr(n - 3, n - 2) * a2 * a3)
        return val

    group = [(p, s) for p in permutations(range(4)) for s in permutations(range(3))]
    memo = {}
    worst = None
    for labs in product(range(3), repeat=6):
        if len(set(labs)) == 1:
            continue
        col = dict(zip(EDGES, labs))
        tot = Fr(0)
        for p, s in group:
            g = {tuple(sorted((p[i], p[j]))): s[col[(i, j)]] for i, j in EDGES}
            key = tuple(g[e] for e in EDGES)
            if key not in memo:
                memo[key] = F(g)
            tot += memo[key]
        worst = tot if worst is None else max(worst, tot)
    assert worst <= 0, f"n={n}: Sym F > 0 on some colouring"
    D = (n - 1) * (n - 2) * (n - 3)
    ff = lambda x: x * (x - 1) * (x - 2)
    minJ = None
    for d1, d2 in product(range(77), repeat=2):
        d3 = n - 1 - d1 - d2
        if not 0 <= d3 <= 76:
            continue
        d = (d1, d2, d3)
        J = (cs * Fr(sum(map(ff, d)), 3 * D)
             + ce * Fr(sum(d[i] * (d[i] - 1) * d[j] for i in range(3) for j in range(3) if i != j), 6 * D)
             + ct * Fr(d1 * d2 * d3, D))
        minJ = J if minJ is None else min(minJ, J)
    assert minJ > 0, f"n={n}: J <= 0 at some profile"
    return len(rows), len(squares), float(minJ)


if __name__ == "__main__":
    data = json.loads((Path(__file__).resolve().parent / "r444_squares.json").read_text())
    for cert in data["certificates"]:
        nr, ns, mj = check(cert)
        print(f"R(4,4,4) <= {cert['n']}: {nr} caps, {ns} squares; Sym F <= 0 on all 14 non-monochromatic orbits, "
              f"min J = {mj:.3e} > 0: OK")
