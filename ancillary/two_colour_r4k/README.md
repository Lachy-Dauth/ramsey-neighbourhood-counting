# two_colour_r4k: R(4,21) >= 260 and R(4,24) >= 370

**What it proves.** Two K4-free graphs with small independence number:
* Q313 minus the 54 vertices in `certs/R_4_21_n259_deleted_from_Q313.txt`: 259 vertices, no K4, independence
  number 20. So R(4,21) >= 260 (previously 242 in the survey DS1.18).
* Q457 minus the 88 vertices in `certs/R_4_24_n369_deleted_from_Q457.txt`: 369 vertices, no K4, independence
  number 23. So R(4,24) >= 370 (the survey's general results imply 324; the table has no entry).

Here Q_p is the quartic-residue graph on Z_p, with x ~ y iff x - y is a nonzero fourth power mod p. For
p = 313 and p = 457 we have p = 1 mod 8, so -1 is a fourth power and the graph is undirected. The deletion lists
are the certificate data. `build_power_sub.py` rebuilds each graph (vertices in natural order) and
`verify_all.sh` checks its SHA-256 against the recorded hash of the matrix found by the search.

**Inputs assumed.** None. Both checks are direct and exhaustive.
* `rcheck.c` decides from the adjacency matrix whether there is a clique on s vertices or an independent set on
  t vertices, by branch and bound with a greedy-colouring bound, multithreaded. It uses no symmetry.
* `qpsym.c` proves alpha(Q_p - S) <= k-1 by enumerating representatives of all independent k-sets of Q_p under
  the affine maps x -> ax + b (a a fourth power), then checking that every image meets S. The lemma is in its
  header. For the 369-vertex graph this is the complete check of alpha <= 23. A direct `rcheck ... 4 24` is the
  slow, optional second check (`--full`).

| file | contents |
|---|---|
| `certs/R_4_21_n259_deleted_from_Q313.txt`, `certs/R_4_24_n369_deleted_from_Q457.txt` | the deleted vertex sets |
| `build_power_sub.py` | rebuilds Q_p minus a vertex set (standard library) |
| `rcheck.c`, `qpsym.c` | the exact checkers (C11, POSIX threads) |
| `verify_all.sh` | builds into `build/`, rebuilds both graphs, checks the SHA-256, runs the checks and the negative controls |

SHA-256 of the rebuilt adjacency files: `d8e985da486f9398497342bfaa0185cf31ececb436719a51c7e9205822a5de81`
(259 vertices) and `bdc972d8b3fbf5295e7155806a69ffaf2792d5ad21cc53ea6720004d6e651a8b` (369 vertices).

**How to run** (from any directory; optional last argument: number of threads, default all cores):

    sh verify_all.sh           # rebuild, rcheck (259), qpsym (313/21, 457/24), K4-freeness (369), controls
    sh verify_all.sh --full    # + direct rcheck of the 369-vertex graph for independent 24-sets

**Expected output.** Every line starts with `ok`. The last line is `ALL CHECKS AS EXPECTED`. The negative controls
must fail as expected: independent 20-sets and triangles in the 259-vertex graph, independent 23-sets and
triangles in the 369-vertex graph, an independent 21-set (24-set) once one deleted vertex is restored,
alpha(Q313) >= 21; and alpha(Q313) <= 21 holds.

**Runtime:** 1.5 to 2 min on 10 threads under load (about 9 CPU minutes, mostly rcheck on the 259-vertex graph
and qpsym on Q457). The `--full` direct check took about 9 min on 10 threads. Earlier it took about 2 hours on
2 threads on a heavily loaded machine.
