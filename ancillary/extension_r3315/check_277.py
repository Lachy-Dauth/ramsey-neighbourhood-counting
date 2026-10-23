#!/usr/bin/env python3
"""R(3,3,15) >= 278: rebuild the 277-vertex witness and run the certificate check (standard library only).

  python3 check_277.py [outdir]        (default outdir: build/ next to this file)

1. build_compact.py rebuilds the 277 x 277 colour matrix from R_3_3_15_n277_compact.json; its SHA-256 must be
   05237157a1e135d4fd5dc5632007ee3e429e25ec98bf7c9a762b3557e780b6ad (the hash of the matrix found by the search).
2. The host H (vertices 0..265) must have exactly the green graph of the paper's (3,3,14;266) circulant in
   ../circulants.json, whose green clique number 13 is verified by ../check_circulants.py (Theorem 9.1).  (Its
   red/blue split differs from the paper's; certcheck.py needs only the green clique number of H.)
3. certcheck.py F 266 13 15 must PASS: no red or blue triangle, and no green K15 given omega_green(H) <= 13.
4. Control: certcheck.py F 266 13 14 must FAIL (the witness does contain a green K14).
"""
import hashlib, json, os, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
SHA = '05237157a1e135d4fd5dc5632007ee3e429e25ec98bf7c9a762b3557e780b6ad'


def main(outdir):
    os.makedirs(outdir, exist_ok=True)
    F = os.path.join(outdir, 'R_3_3_15_n277.txt')
    subprocess.run([sys.executable, os.path.join(HERE, 'build_compact.py'), os.path.join(HERE, 'R_3_3_15_n277_compact.json'), F],
                   check=True)
    sha = hashlib.sha256(open(F, 'rb').read()).hexdigest()
    ok = sha == SHA
    print(f'rebuilt {os.path.relpath(F, HERE)}: sha256 {sha} ({"matches" if ok else "MISMATCH"})')
    M = [l.strip() for l in open(F) if l.strip()]
    w = next(w for w in json.load(open(os.path.join(HERE, '..', 'circulants.json')))['witnesses'] if w['n'] == 266)
    n0, nonG = w['n'], set(w['A']) | set(w['B'])
    dist = lambda i, j: min((i - j) % n0, (j - i) % n0)
    host = all((M[i][j] == '2') == (dist(i, j) not in nonG) for i in range(n0) for j in range(n0) if i != j)
    print(f'host = vertices 0..{n0 - 1}: green graph {"equals" if host else "DIFFERS FROM"} that of the (3,3,14;266) circulant '
          f'of circulants.json (green clique number 13 by check_circulants.py)')
    ok &= host
    for k, want in ((15, 'PASS'), (14, 'FAIL')):
        out = subprocess.run([sys.executable, os.path.join(HERE, 'certcheck.py'), F, str(n0), '13', str(k)],
                             capture_output=True, text=True).stdout.strip().splitlines()
        res = out[-1] if out else ''
        good = res.startswith('RESULT: ' + want)
        tag = 'claim' if want == 'PASS' else 'control'
        print(f'certcheck k={k} ({tag}, expect {want}): {res}' + ('' if good else '   <-- UNEXPECTED'))
        if want == 'PASS': print('  ' + '\n  '.join(out[:-1]))
        ok &= good
    print('R(3,3,15) >= 278: ALL CHECKS PASSED' if ok else 'R(3,3,15) >= 278: SOME CHECK FAILED')
    return ok


if __name__ == '__main__':
    sys.exit(0 if main(sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, 'build')) else 1)
