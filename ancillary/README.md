# Ancillary files

For the paper *Neighbourhood counting and new bounds for small three-colour Ramsey numbers* (in the git repository
https://github.com/Lachy-Dauth/ramsey-neighbourhood-counting it is in `../paper/`). References below such as
"Theorem 8.2" are to its numbering. The code and data are under the MIT licence (`LICENSE`).

This folder holds, for every computational claim of the paper, the data and an exact checker. You need only the
Python 3 standard library and a C++17 compiler. The exceptions are
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
| `verify_hand_proofs.py` | the main numerical steps of the hand proofs (not every intermediate value): 88, 129, 179, the m6/m7 tables, 155, 276, 346, the triangle identities on all 27 coloured triangles, the comparison values (Sections 4, 6) | Q | 1 s |
| `bootstrap.py` | regenerates `tables.json`, the certificate of the ladder (Section 5) | - | |
| `tables.json`, `verify_bootstrap.py` | independent exact check of `tables.json`: 4240 rows, 420,545 degree cases, R(3,3,k) <= 88, 129, 179, 247, 315, 407, 512, 628, 756, 901 for k = 6..15 (Theorem 5.2) | Q | 10 s |
| `verify_cascade.py` | R(3,4,7) <= 456, R(3,4,8) <= 700, R(3,5,6) <= 683 (and 276, 346), with the survey's Table Ib values (Proposition 6.5) | Q | 1 s |
| `verify_cascade_published_only.py` | the same with published two-colour inputs only: 276, 458, 705, 346, 685 (Proposition 6.5) | Q | 1 s |
| `verify_r444.py` | identities (I)-(III), R(4,4,4) <= 226 (Theorem 7.4) and identity (7) with the J values, R(4,4,4) <= 225 (Theorem 7.5) | Q | 5 s |
| `r444_squares.json`, `verify_r444_squares.py` | four-vertex multi-square certificates for R(4,4,4) <= 224, 223, 222, 221, 220, 219 (Section 7) | Q | 4 s |
| `circulants.json`, `check_circulants.py`, `clique_check.cpp` | the five circulant witnesses: R(3,3,9) >= 133, R(3,3,11) >= 183, R(3,3,12) >= 203, R(3,3,13) >= 232, R(3,3,14) >= 267. Sum-free checks, full matrices `R_3_3_k_n*.txt` (regenerated; diagonal written as 0 and ignored) with SHA-256, and an exact green clique number k-1 through vertex 0 (Theorem 9.1) | Q | 4 s |
| `check_colouring_full.cpp` | independent second check: a direct clique search of each full matrix, with no symmetry reduction (Theorem 9.1). Usage: `./check_colouring_full R_3_3_14_n266.txt 3 3 14` | F | 1 s, 6 s, 17 s, 64 s, 5 min for n = 132, 182, 202, 231, 266 |
| `flag5_r444/` | R(4,4,4) <= 204 (five-vertex certificate, `check5.py`; Section 8) | Q | 35-45 s |
|  | R(4,4,4) <= 199 and R(4,4,4) <= 198 (five-vertex certificates, `check5.py`; Theorem 8.2) | F | 2.5-3 min each |
|  | R(4,4,4) <= 198 again with the six-vertex checker `check6.py` (numpy; skipped if numpy is absent) | F | 7 min |
|  | negative controls (`negative5.py`, `reuse5.py`, `negative6.py`); `identity_eloc.py` | C; Q | 6 + 4 + 22 min; 3 s |
| `flag5_r34k/` | R(3,4,4) <= 73, R(3,4,5) <= 137, R(4,4,4) <= 200, R(3,5,5) <= 316, R(3,4,6) <= 247, R(3,4,7) <= 409, R(3,5,6) <= 622, R(3,4,8) <= 626, and with the starred inputs R(3,4,6) <= 245, R(3,4,7) <= 406, R(3,5,6) <= 619, R(3,4,8) <= 625 (manifest of 13 five-vertex mixture certificates; Theorem 8.3). The extra one, `R355_316_r344le77.json`, proves R(3,5,5) <= 316 again without the input R(3,4,4) <= 73 (proof of Theorem 8.3) | F | 3-5 min |
|  | negative controls on all 13 certificates; positive controls on explicit colourings | C | 30 min; 8 min |
| `flag_r33k/` | R(3,3,6) <= 86, R(3,3,7) <= 125, R(3,3,8) <= 174 from three standalone five-vertex exclusion certificates (Theorem 8.4) | Q | 25 s |
|  | the unified flag ladder: R(3,3,k) <= 86, 125, 173, 241, 309, 401, 505, 620, 748, 892 for k = 6..15 (155 flag certificates and 4178 ladder rows; Theorem 8.5) | F | 7.5 min |
|  | controls of the chain (`controls_unified.py`) and of four five-vertex certificates (`controls5.py`); soundness test on a real colouring (`sanity5.py`) | C | 11 + 22 min; 35 s |
| `extension_r3315/` | R(3,3,15) >= 278: the 277-vertex witness rebuilt from its compact description (SHA-256), and the certificate check that reduces it to the green clique number 13 of the n = 266 circulant (Theorem 9.3) | Q | 1 s |
|  | direct exact searches on the full matrix (kcheck: no red/blue K3, no green K15; glue_check: green clique number 14) and negative controls | F | 4 min in total |
|  | the paper's `check_colouring_full.cpp` on the 277-vertex matrix | F | 51 min |
| `lean/` | Lean 4 formalisation of two facts used in Lemma 3.1 of A (described in Section 10): the local step of the apex lemma and the unique-apex identity, no `sorry`. Needs Lean 4 and Mathlib; see `lean/README.md` | - | |
| `run_all.sh` | runs everything above | | |

The graph-theoretic premises, such as the local caps and the counting lemmas, are proved in the paper. These
programs check the finite arithmetic and the identities that the proofs reduce to. The published Ramsey inputs
(Table 3 of the paper, and for the new certificates the inputs listed in each subfolder's README) are premises.
They are not re-derived here.
