# extension_r3315: R(3,3,15) >= 278

**What it proves.** There is a (3,3,15;277)-colouring, so R(3,3,15) >= 278 (the survey lists 269). The witness
F extends a 266-vertex split circulant H by eleven new vertices. Six of them are copies of the anchors
0, 5, 70, 131, 140, 201; five are green to H except towards the anchors. `R_3_3_15_n277_compact.json` describes
F completely: the red and blue distance sets of H, the anchors, the colours of the five non-copy vertices
towards the anchors, and the 11 x 11 colour matrix of the new vertices. `build_compact.py` rebuilds the full
277 x 277 matrix from it.

**Inputs assumed.** The only premise of the certificate check is that the green clique number of H is 13.
H has the same green graph as the paper's (3,3,14;266) circulant in `../circulants.json`; only its red/blue
split differs. That circulant's green clique number is 13, proved by `../check_circulants.py` (A, Theorem 9.1) and
again by the direct search `../check_colouring_full.cpp` in `run_all.sh --full`. `check_277.py` checks that the
green graphs agree. The direct searches below need no premise at all.

| file | contents |
|---|---|
| `R_3_3_15_n277_compact.json` | the witness, compactly (872 bytes) |
| `build_compact.py` | rebuilds the 277 x 277 matrix (rows of 0 red / 1 blue / 2 green; the diagonal is written as 0 and ignored) |
| `check_277.py` | rebuild, SHA-256 against the recorded hash, host check, `certcheck.py` with k = 15 (must PASS) and k = 14 (control, must FAIL) |
| `certcheck.py` | certificate check (Lemma "certifiers"). It checks directly that red and blue are triangle-free. Then, for every green clique S of new vertices, it checks \|S\| + 13 - omega(certifiers of S) <= 14 |
| `kcheck.cpp` | exact bitset branch-and-bound clique search on the full matrix, without symmetry assumptions |
| `glue_check.cpp` | exact green clique number via the split host + new vertices (max over S of \|S\| + omega(common green neighbourhood of S in H)) |
| `controls.py` | negative controls: kcheck -max 2 gives exactly 14; one recoloured edge creates a red K3 and another a green K15, and kcheck finds both |
| `check_all.sh` | runs all of the above (`--full` for the compiled searches) |

SHA-256 of the rebuilt matrix: `05237157a1e135d4fd5dc5632007ee3e429e25ec98bf7c9a762b3557e780b6ad`.

**How to run** (from any directory):

    sh check_all.sh            # rebuild + certcheck (under a second)
    sh check_all.sh --full     # + kcheck, glue_check, controls (C++ compiler)

**Expected output.**

    rebuilt build/R_3_3_15_n277.txt: sha256 05237157...b6ad (matches)
    host = vertices 0..265: green graph equals that of the (3,3,14;266) circulant of circulants.json ...
    certcheck k=15 (claim, expect PASS): RESULT: PASS (no red/blue K3; green clique number <= 14 given omega_green(H) <= 13)
    certcheck k=14 (control, expect FAIL): RESULT: FAIL (...)
    R(3,3,15) >= 278: ALL CHECKS PASSED
    --full: kcheck: colour 0, 1 forbidden=K3 clique_found=false; colour 2 forbidden=K15 clique_found=false
            glue_check: clique_number=14;  controls: control 1, 2, 3 PASS

**Runtime** (10-core laptop): default under 1 s. kcheck about 1 min, glue_check about 2 min, controls about
1 min (about 4 min for `--full` in all; more under load). `run_all.sh --full` also runs the paper's direct checker
`../check_colouring_full.cpp` on the rebuilt matrix. It finds no red or blue K3 and no green K15, and its green
search took 51 min (2,532,575,066 nodes).
