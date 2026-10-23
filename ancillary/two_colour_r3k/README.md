# two_colour_r3k: upper bounds for R(3,k), k <= 50

**What it proves.** The certificates bound e(3,k,n) from below, level by level, and deduce caps R(3,k) <= B_k.
They use the Graver-Yackel inequality with lower convex hulls and the Radziszowski-Kreher bound, and an exact
degree-sequence enumeration with a transport LP (Farkas certificates) at the binding orders. The checker also
accepts vertex-deletion rows, but neither chain uses one.

| k | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 | 32 | 33 | 34 | 35 | 36 | 37..50 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| R(3,k) <= (with [Back3]) | 200 | 215 | 230 | 245 | 261 | 278 | 295 | 312 | 331 | 349 | 369 | 389 | 408 | as below |
| R(3,k) <= ([GR13] only) | 201 | 216 | 231 | 247 | 264 | 280 | 297 | 315 | 333 | 351 | 370 | 389 | 409 | as below |

For 37 <= k <= 50 both chains give 429, 450, 471, 492, 513, 536, 559, 582, 606, 630, 654, 679, 704, 729. The survey
lists no upper bounds for k >= 24. For 11 <= k <= 23 the chains improve no bound of the survey; they reproduce
the following with checkable proofs. From [GR13] alone: R(3,17) <= 109 and R(3,20) <= 145. With [Back3]: R(3,16) <= 97, R(3,19) <= 132, R(3,23) <= 185.
`run_all.sh` passes all of these as `--claim k,B`. The checker fails if a claimed cap is not established.

**Inputs assumed** (cited as in the source report):
* [GR13] J. Goedgebeur and S. Radziszowski, *New computational upper bounds for Ramsey numbers R(3,k)*,
  Electron. J. Combin. 20(1) (2013) #P30, arXiv:1210.5826v4: Tables 3, 4, 5 (exact values and lower bounds of
  e(3,k,n), k <= 10) and Theorem 2 (Radziszowski-Kreher). They are transcribed from the arXiv text in
  `checker/gr13_table3.txt`, `gr13_table4.txt`, `gr13_table5.txt`.
* R(3,10) <= 42 [GR13, Theorem 6], as in Theorem 2.1 of paper B. The commands below pass `--r310 42`, as
  `run_all.sh` does. Angeltveit's R(3,10) <= 41 (Electron. J. Combin. 32(4) (2025) #P4.30, arXiv:2401.00392)
  is not needed: without `--r310` the checker uses 41, and the result is the same. The controls include a run
  with `--r310 42` and a weakened e(3,10,41), which must be rejected.
* [Back3] J. Backelin, *Edge number report 1*, arXiv:1410.1843v1, Section 5 table: lower bounds for e(3,l;n),
  l = 10..13, 35 <= n <= 43, transcribed in `checker/cited_extra.txt` (only the chain `r3k_back3_seq_k50.json`
  uses them).

| file | contents |
|---|---|
| `certs/r3k_back3_seq_k50.json` | chain with [GR13] + [Back3] inputs (13376 rows) |
| `certs/r3k_pub_seq_k50.json` | chain with [GR13] inputs only (13403 rows) |
| `certs/README.md` | notes on the certificates |
| `checker/check_r3k_v2.py` | exact checker (standard library). It imports `check_r3k.py` for the input parser and the basic row types |
| `checker/check_r3k.py` | version-1 checker (row types 'trivial', 'thm2', 'edge', 'delete', ...; the [GR13] parser) |
| `checker/gr13_table*.txt`, `checker/cited_extra.txt` | the cited inputs |
| `checker/negative_controls_v2.py` | weakened [GR13] input, [Back3] dropped, zeroed Farkas multiplier, missing sequence certificate, value + 1, claim one better than proved, R(3,10) <= 42 with a weakened e(3,10,41): all must be rejected; two robustness cases must be accepted |
| `checker/negative_controls_high.py` | forged cap R(3,24) <= 199, edge rows + 1 at k = 30 and 45, weakened e(3,10,40): all must be rejected |

**How to run** (from this folder):

    python3 checker/check_r3k_v2.py --r310 42 certs/r3k_back3_seq_k50.json --claim 16,97 --claim 19,132 --claim 23,185 --claim 24,200 --claim 50,729
    python3 checker/check_r3k_v2.py --r310 42 certs/r3k_pub_seq_k50.json --no-back3 --claim 17,109 --claim 20,145 --claim 24,201
    python3 checker/negative_controls_v2.py certs/r3k_back3_seq_k50.json
    python3 checker/negative_controls_v2.py certs/r3k_pub_seq_k50.json
    python3 checker/negative_controls_high.py certs/r3k_back3_seq_k50.json

**Expected output.** One line `k=..: R(3,k) <= B verified (...)` per level, then

    ACCEPT: 13376 rows; 53 (k,n,e) triples excluded by enumeration, 765 degree sequences certified          (back3)
    ACCEPT: 13403 rows; 50 (k,n,e) triples excluded by enumeration, 766 degree sequences certified          (published only)

The controls end with `ALL NEGATIVE CONTROLS BEHAVE` and `ALL HIGH-LEVEL CONTROLS REJECTED`.

**Runtime:** about 2 s per chain and about 25 s for all the controls.
