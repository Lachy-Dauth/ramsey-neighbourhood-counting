"""Check the circulant witnesses of Theorem 9.1.  Standard library only (plus a C++ compiler
for the clique search).  Run: python3 check_circulants.py

1. sum-free check: red and blue have no triangle;
2. writes each full adjacency matrix (0 = red, 1 = blue, 2 = green; diagonal written as 0 and ignored) and prints its SHA-256;
3. compiles clique_check.cpp and runs an exact branch-and-bound search for the largest green
   clique through vertex 0 (enough, by vertex-transitivity); it must equal k-1.
"""
import hashlib, json, subprocess, sys
from pathlib import Path
HERE = Path(__file__).resolve().parent
data = json.loads((HERE / "circulants.json").read_text())["witnesses"]
exe = HERE / "clique_check"
subprocess.run(["c++", "-O3", "-std=c++17", "-o", str(exe), str(HERE / "clique_check.cpp")], check=True)
for w in data:
    n, k, A, B = w["n"], w["k"], set(w["A"]), set(w["B"])
    assert not (A & B) and max(A | B) <= n // 2
    for D in (A, B):
        S = {d % n for d in D} | {(-d) % n for d in D}
        assert not any((x - y) % n in S for x in S for y in S if x != y), "triangle found"
    dist = lambda i, j: min((i - j) % n, (j - i) % n)
    rows = ["".join("0" if i == j else ("0" if dist(i, j) in A else "1" if dist(i, j) in B else "2")
                    for j in range(n)) for i in range(n)]
    out = HERE / f"R_3_3_{k}_n{n}.txt"
    out.write_text("\n".join(rows) + "\n")
    sha = hashlib.sha256(out.read_bytes()).hexdigest()
    inp = f"{n} {k} " + " ".join(map(str, sorted(A))) + " -1 " + " ".join(map(str, sorted(B))) + " -1\n"
    res = subprocess.run([str(exe)], input=inp, capture_output=True, text=True, check=True).stdout.strip()
    assert "VALID" in res and f"max green clique = {k-1} " in res, res
    print(f"n={n} k={k}: red/blue triangle-free; {res.split(';')[0].split(': ')[1]}; sha256 {sha[:16]}...")
print("all witnesses verified")
