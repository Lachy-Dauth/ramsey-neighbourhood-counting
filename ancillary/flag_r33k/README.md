# flag_r33k: the unified flag ladder for R(3,3,k), 6 <= k <= 15

**What it proves.**

| k | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 |
|---|---|---|---|---|---|---|---|---|---|---|
| R(3,3,k) <= | 86 | 125 | 173 | 241 | 309 | 401 | 505 | 620 | 748 | 892 |
| paper's ladder (Theorem 5.2) | 88 | 129 | 179 | 247 | 315 | 407 | 512 | 628 | 756 | 901 |

The chain `certificates/unified/chain_final.json` interleaves, level by level, 155 exact flag certificates with
the rows of the ladder of Section 5. These are 117 four-vertex certificates (`k3`..`k6`, `ext/`) and 38 five-vertex
certificates (`five/`). The certificates are density certificates (lower bounds on the number of red-or-blue edges
of a (3,3,k;n)-colouring) and exclusion certificates. The rows are the lower bounds m_k(n) on e(H), with the line
bounds of Lemmas 3.2-3.5. `check_unified.py` accepts a row or a bound B_k only if it follows from the paper's
lemmas and from values proved earlier in the same run. Every R(3,3,j) for j >= 6 starts at infinity, so every
bound used is proved in the chain. The docstring of `check_unified.py` gives the rules. Those of
`check_r33k.py` (four-vertex) and `check_r33k5.py` (five-vertex) give the certificate semantics.

Separately, three five-vertex exclusion certificates prove R(3,3,6) <= 86, R(3,3,7) <= 125 and R(3,3,8) <= 174
without any ladder rows (`check_r33k5.py`, standalone; the quick check).

All 155 certificate files that the chain references are shipped. Besides them, `certificates/unified/` holds the
chain `chain_final.json`, the flag-free chain `chain_noflag.json` and `flag_manifest_final.txt` (the list of the 155
files). The chain checker
opens every listed file, so none can be dropped without editing the chain. Some are superseded within the chain:
* 28 four-vertex density certificates (k5/dens_39, ext/k6/dens_64..71, k6/dens_68..86) are dominated by a larger
  m for the same (k,n) (360 KB);
* the exclusions k6/excl_87, five/k7/excl_126 and five/k8/excl_175 are dominated by stronger bounds (245 KB);
* the five-vertex density certificates five/k11/dens_387 (m = 17656) and five/k13/dens_594 (m = 36621) are
  dominated by the line bounds of the rows (11,387) and (13,594), m = 17678 and 36626 (8 KB).

Together these are under 1 MB of the 13 MB. The chain was left exactly as it was checked. The bulk is `five/`
(12 MB): the five-vertex certificates at levels 6, 7 and 8 that carry the improvement.
`certificates/SHA256SUMS` lists the SHA-256 of every certificate and of the chain.

**Inputs assumed** (Table 3 of the paper; the dictionaries `R2` and `R33` in `check_r33k.py`):
R(3,j) for j = 3..15 (6, 9, 14, 18, 23, 28, 36, and the upper bounds 41, 50, 59, 68, 77, 87),
R(3,3,3) = 17, R(3,3,4) = 30, R(3,3,5) <= 57. In the standalone checks the dictionary starts from the hand-proved
R(3,3,6) <= 88, R(3,3,7) <= 129, R(3,3,8) <= 179, but these never enter when the three certificates are checked in
the given order: each verified exclusion lowers its entry, and each certificate uses only the inputs above and the
exclusions verified before it (green caps D3 = 56, 85, 124). Checked singly or out of order, a certificate may use
the hand-proved values.

| file | contents |
|---|---|
| `check_unified.py` | the chain checker (standard library). It uses `check_r33k.py` and `check_r33k5.py` for the flag certificates |
| `check_r33k.py`, `check_r33k5.py` | exact checkers for four- and five-vertex certificates (also usable standalone) |
| `certificates/unified/chain_final.json` | the chain: per level, the flag certificates (paths relative to `certificates/`), the rows and the exclusion method |
| `certificates/unified/chain_noflag.json` | the same ladder built with no flag certificates (it reproduces the paper's bounds; used by the controls) |
| `certificates/unified/flag_manifest_final.txt` | the list of the 155 flag certificates that `chain_final.json` references (not read by the checkers) |
| `certificates/k3`..`k6`, `ext/`, `five/` | the 155 flag certificates |
| `controls_unified.py` | controls of the chain: accepted with its bounds; the flag-free chain gives exactly the paper's bounds; removing the flags, raising a row by one, B_7 - 1 by Psi, B_6 - 1 by flag and a corrupted density certificate are all rejected; the real colourings obtained from the circulant witnesses in `../circulants.json` (iterated green neighbourhoods and greedy deletion) satisfy every accepted m_j(s) |
| `controls5.py` | negative controls for five-vertex certificates in the state of the chain |
| `sanity5.py` | soundness test of the five-vertex formulas (stars, squares, every row) on the real (3,3,6;26)-colouring obtained from the n = 132 witness |

**How to run** (from this folder):

    python3 check_r33k5.py certificates/five/k6/excl_86.json certificates/five/k7/excl_125.json certificates/five/k8/excl_174.json
    python3 check_unified.py                       # = check_unified.py certificates/unified/chain_final.json
    python3 controls_unified.py                    # chain_final.json and chain_noflag.json
    python3 controls5.py certificates/unified/chain_final.json certificates/five/k6/excl_86.json certificates/five/k7/excl_125.json certificates/five/k7/dens_120.json certificates/five/k8/excl_174.json
    python3 sanity5.py

**Expected output.** The standalone check ends with `ALL VALID`. `check_unified.py` prints one line per level, then

    155 flag certificates, 4178 ladder rows, 414377 admissible degree cases
    CHAIN VALID
    bounds: {3: 17, 4: 30, 5: 57, 6: 86, 7: 125, 8: 173, 9: 241, 10: 309, 11: 401, 12: 505, 13: 620, 14: 748, 15: 892}

The controls end with `ALL CONTROLS PASSED`, `ALL CONTROLS5 PASSED` and `SANITY5 PASSED`. The real-colouring test
of `controls_unified.py` reports `14235 (level, order) tests, 0 failures, least slack 0` with the five witnesses
of `../circulants.json`. Restricted to the four witnesses k = 9, 11, 12, 14, it gives the 11278 tests of the
original numpy version.

**Runtime** (10-core laptop, under load): standalone 22 s; chain 7.5 min; sanity5 35 s. `controls_unified.py`
(11 min) and `controls5.py` (22 min) re-run the chain several times; flag verdicts are memoised.
