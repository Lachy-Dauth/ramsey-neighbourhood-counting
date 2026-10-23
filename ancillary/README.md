# Ancillary files

For the two papers **[A]** *Neighbourhood counting and new bounds for small three-colour Ramsey numbers* and **[B]** *New bounds for small two- and four-colour Ramsey numbers* (in the git repository
https://github.com/Lachy-Dauth/ramsey-neighbourhood-counting they are in `../paper/`). References below such as
"A, Theorem 8.2" are to their numbering. The code and data are under the MIT licence (`LICENSE`).

This folder holds, for every computational claim of the papers, the data and an exact checker. You need only the
Python 3 standard library, a C++17 compiler and a C compiler with POSIX threads. The exceptions are
`flag5_r444/checkers/check6.py`, an optional second checker, and its controls `flag5_r444/controls/negative6.py`,
which need numpy; `run_all.sh` skips them, and says so, if numpy is missing. Every script can be run from any
directory, because all paths are relative to the script.

    sh run_all.sh              # quick mode, about 4 minutes (in the git repository also: make verify, which CI runs)
    sh run_all.sh --full       # + the long checks and the direct clique searches (1.5-2 hours; in the git repository: make verify-full)
    sh run_all.sh --controls   # the expensive negative and positive controls (about 2 hours; in the git repository: make verify-controls)

`run_all.sh` stops with a non-zero exit status at the first failing check, and prints the wall time of every
step. Each subfolder has a README with what it proves, the inputs it assumes, how to run it, the expected output
and the runtime.

Runtimes are wall times on a 10-core laptop (Python 3.14), measured while other checks ran in parallel (load
average 10-30), so an idle machine is faster. Mode: Q = quick, F = `--full`, C = `--controls`, - = not run by
`run_all.sh`.

| file or folder | result checked | mode | runtime |
|---|---|---|---|
| `verify_hand_proofs.py` | the main numerical steps of the hand proofs (not every intermediate value): 88, 129, 179, the m6/m7 tables, 155, 276, 346, the triangle identities on all 27 coloured triangles, the comparison values (A, Sections 4, 6) | Q | 1 s |
| `bootstrap.py` | regenerates `tables.json`, the certificate of the ladder (A, Section 5) | - | |
| `tables.json`, `verify_bootstrap.py` | independent exact check of `tables.json`: 4240 rows, 420,545 degree cases, R(3,3,k) <= 88, 129, 179, 247, 315, 407, 512, 628, 756, 901 for k = 6..15 (A, Theorem 5.2) | Q | 10 s |
| `verify_cascade.py` | R(3,4,7) <= 456, R(3,4,8) <= 700, R(3,5,6) <= 683 (and 276, 346), with the survey's Table Ib values (A, Proposition 6.5) | Q | 1 s |
| `verify_cascade_published_only.py` | the same with published two-colour inputs only: 276, 458, 705, 346, 685 (A, Proposition 6.5) | Q | 1 s |
| `verify_r444.py` | identities (I)-(III), R(4,4,4) <= 226 (A, Theorem 7.4) and identity (7) with the J values, R(4,4,4) <= 225 (A, Theorem 7.5) | Q | 5 s |
| `r444_squares.json`, `verify_r444_squares.py` | four-vertex multi-square certificates for R(4,4,4) <= 224, 223, 222, 221, 220, 219 (A, Section 7) | Q | 4 s |
| `circulants.json`, `check_circulants.py`, `clique_check.cpp` | the five circulant witnesses: R(3,3,9) >= 133, R(3,3,11) >= 183, R(3,3,12) >= 203, R(3,3,13) >= 232, R(3,3,14) >= 267. Sum-free checks, full matrices `R_3_3_k_n*.txt` (regenerated; diagonal written as 0 and ignored) with SHA-256, and an exact green clique number k-1 through vertex 0 (A, Theorem 9.1) | Q | 4 s |
| `check_colouring_full.cpp` | independent second check: a direct clique search of each full matrix, with no symmetry reduction (A, Theorem 9.1). Usage: `./check_colouring_full R_3_3_14_n266.txt 3 3 14` | F | 1 s, 6 s, 17 s, 64 s, 5 min for n = 132, 182, 202, 231, 266 |
| `flag5_r444/` | R(4,4,4) <= 204 (five-vertex certificate, `check5.py`; A, Section 8) | Q | 35-45 s |
|  | R(4,4,4) <= 199 and R(4,4,4) <= 198 (five-vertex certificates, `check5.py`; A, Theorem 8.2) | F | 2.5-3 min each |
|  | R(4,4,4) <= 198 again with the six-vertex checker `check6.py` (numpy; skipped if numpy is absent) | F | 7 min |
|  | negative controls (`negative5.py`, `reuse5.py`, `negative6.py`); `identity_eloc.py` | C; Q | 6 + 4 + 22 min; 3 s |
| `flag5_r34k/` | R(3,4,4) <= 73, R(3,4,5) <= 137, R(4,4,4) <= 200, R(3,5,5) <= 316, R(3,4,6) <= 247, R(3,4,7) <= 409, R(3,5,6) <= 622, R(3,4,8) <= 626, and with the starred inputs R(3,4,6) <= 245, R(3,4,7) <= 406, R(3,5,6) <= 619, R(3,4,8) <= 625 (manifest of 12 five-vertex mixture certificates; A, Theorem 8.3) | F | 3-4.5 min |
|  | negative controls on all 12 certificates; positive controls on explicit colourings | C | 28 min; 8 min |
| `flag_r33k/` | R(3,3,6) <= 86, R(3,3,7) <= 125, R(3,3,8) <= 174 from three standalone five-vertex exclusion certificates (A, Theorem 8.4) | Q | 25 s |
|  | the unified flag ladder: R(3,3,k) <= 86, 125, 173, 241, 309, 401, 505, 620, 748, 892 for k = 6..15 (155 flag certificates and 4178 ladder rows; A, Theorem 8.5) | F | 7.5 min |
|  | controls of the chain (`controls_unified.py`) and of four five-vertex certificates (`controls5.py`); soundness test on a real colouring (`sanity5.py`) | C | 11 + 22 min; 35 s |
| `extension_r3315/` | R(3,3,15) >= 278: the 277-vertex witness rebuilt from its compact description (SHA-256), and the certificate check that reduces it to the green clique number 13 of the n = 266 circulant (A, Theorem 9.3) | Q | 1 s |
|  | direct exact searches on the full matrix (kcheck: no red/blue K3, no green K15; glue_check: green clique number 14) and negative controls | F | 4 min in total |
|  | the paper's `check_colouring_full.cpp` on the 277-vertex matrix | F | 51 min |
| `two_colour_r3k/` | R(3,k) <= B_k for k <= 50 (two chains: [GR13] inputs only, and with Backelin's e(3,l;n) bounds), e.g. R(3,24) <= 201 ([GR13] only) or 200 (with [Back3]), R(3,50) <= 729; R(3,16) <= 97, R(3,17) <= 109, R(3,19) <= 132, R(3,20) <= 145, R(3,23) <= 185 (B, Theorem 2.1; the values for k <= 23 only reproduce known bounds); negative controls | Q | 30 s |
| `two_colour_r4k/` | R(4,21) >= 260 and R(4,24) >= 370: graphs rebuilt from the deletion lists (SHA-256), rcheck and qpsym, negative controls (B, Theorem 3.1) | Q | 2 min (10 threads) |
|  | direct rcheck of the 369-vertex graph for independent 24-sets | F | 9 min (10 threads) |
| `lean/` | Lean 4 formalisation of two facts used in Lemma 3.1 of A (described in A, Section 10): the local step of the apex lemma and the unique-apex identity, no `sorry`. Needs Lean 4 and Mathlib; see `lean/README.md` | - | |
| `run_all.sh` | runs everything above | | |

The graph-theoretic premises, such as the local caps and the counting lemmas, are proved in the papers. These
programs check the finite arithmetic and the identities that the proofs reduce to. The published Ramsey inputs
(Table 3 of A, and for the new certificates the inputs listed in each subfolder's README) are premises.
They are not re-derived here.
