# flag5_r34k: five-vertex mixture certificates for R(3,4,4), R(3,4,5), R(4,4,4), R(3,5,5), R(3,4,k), R(3,5,6)

**What it proves.** Thirteen exact five-vertex flag certificates with a degree-profile mixture, for general
t = (t0,t1,t2): one for each of the twelve bounds below, and a variant of the R(3,5,5) certificate that does not
use R(3,4,4) <= 73 (see "The variant for R(3,5,5)" below). They are chained by `certificates/manifest.json`:

| bound | certificate | uses (besides the base inputs) |
|---|---|---|
| R(3,4,4) <= 73 | `R344_73.json` | - |
| R(3,4,5) <= 137 | `R345_137.json` | - |
| R(4,4,4) <= 200 | `R444_200.json` | - |
| R(3,5,5) <= 316 | `R355_316.json` | R(3,4,4) <= 73, R(3,4,5) <= 137 |
| R(3,5,5) <= 316 (variant) | `R355_316_r344le77.json` | R(3,4,5) <= 137 only |
| R(3,4,6) <= 247 | `R346_247.json` | R(3,4,4) <= 73, R(3,4,5) <= 137 |
| R(3,4,7) <= 409 | `R347_409.json` | ... and R(3,4,6) <= 247 |
| R(3,5,6) <= 622 | `R356_622.json` | ... and R(3,4,6) <= 247, R(3,5,5) <= 316 |
| R(3,4,8) <= 626 | `R348_626.json` | ... and R(3,4,6) <= 247, R(3,4,7) <= 411 |
| R(3,4,6) <= 245 [S] | `R346_245_S.json` | ... and R(4,6) <= 40* |
| R(3,4,7) <= 406 [S] | `R347_406_S.json` | ... and R(4,6) <= 40*, R(4,7) <= 58* |
| R(3,5,6) <= 619 [S] | `R356_619_S.json` | ... and R(4,6) <= 40*, R(5,6) <= 85* |
| R(3,4,8) <= 625 [S] | `R348_625_S.json` | ... and R(3,4,6) <= 245, R(3,4,7) <= 409, R(4,6) <= 40*, R(4,7) <= 58*, R(4,8) <= 79* |

[S] marks the starred chain. It also uses the unpublished two-colour bounds of Angeltveit and McKay (marked * here,
personal communication as reported in the survey DS1.18, Table Ib). The other entries (chain U) use published
inputs only. `verify_manifest.py` checks two things: each certificate is valid with exactly the inputs listed for
it, and every new input is proved by an earlier entry of the manifest or is one of the four starred values in an
[S] entry.

**Inputs assumed** (the tables `R2` and `R3_BASE` in `check/check_flag5_mix.py`):
* two-colour values: R(3,3..10) = 6, 9, 14, 18, 23, 28, 36 and <= 41; R(4,4) = 18, R(4,5) = 25, R(4,6) <= 41,
  R(4,7) <= 61, R(4,8) <= 84, R(5,5) <= 46, R(5,6) <= 87 (the published bounds);
* three-colour values: R(3,3,3) = 17 [GG55], R(3,3,4) = 30 [CFIM16], R(3,3,5) <= 57 and R(3,4,4) <= 77
  (from the recurrence, as listed in the survey); the paper's own theorems R(3,3,6) <= 88, R(3,3,7) <= 129,
  R(3,3,8) <= 179, R(3,4,5) <= 155, R(3,4,6) <= 276, R(3,5,5) <= 346, and R(3,4,7) <= 458 (Proposition 6.5,
  published inputs only). Other values enter only as manifest inputs (`--input`), each proved by an earlier entry.

Every cap constant is recomputed from these by Lemma 2.1 and the intersection rule in the checker's docstring.

**The variant for R(3,5,5).** `R355_316_r344le77.json` is `R355_316.json` with one cap constant recomputed for
the base value R(3,4,4) <= 77 in place of the input R(3,4,4) <= 73. It is the constant of the one row whose cap
involves R(3,4,4): the 'int' row with rho = (0,0,1,1,0,2), J = (2,3), a = (1,2) (entry 34 of `rows`, counting from 0), whose
q = R(3,4,4) - 1 is 72 in `R355_316.json` and 76 here. Nothing else differs (the two files differ in one byte).
The checker accepts it with the input R(3,4,5) <= 137 only, with the same margin 1.4675e-7, and R(3,4,5) <= 137
itself uses base inputs only. So R(3,5,5) <= 316 does not depend on R(3,4,4) <= 73 (A, proof of Theorem 8.3).
The file's `R3` field is copied unchanged from `R355_316.json`, so it still lists R(3,4,4) <= 73. The checker
ignores that field: the inputs that count are those given with `--input` or listed in the manifest.

| file | contents |
|---|---|
| `certificates/*.json`, `certificates/manifest.json` | the thirteen certificates and the chain |
| `check/check_flag5_mix.py` | exact checker for one certificate (standard library). Docstring: all definitions |
| `check/verify_manifest.py` | runs the checker on every manifest entry with exactly its inputs, and checks the provenance of the inputs |
| `check/check_flag4_mix.py` | four-vertex version. `verify_manifest.py` imports it (its Ramsey lookup is used for Lemma 2.1 entries; this manifest has none) |
| `check/controls_manifest.py` | negative controls for every manifest entry (edited constants, n-1, edited caps, inputs dropped, perturbed multipliers) |
| `check/controls_flag5.py`, `controls_flag5_333.py`, `controls_flag5_444.py`, `controls_flag5_tk.py` | positive (soundness) controls. On explicit t-avoiding colourings (subsets of the circulants in `data/`, and the (3,3,3;16) colouring), every row has expectation <= 0 under the exact five-vertex law, and the star and square expansions hold exactly |
| `data/circ_344.json`, `circ_345.json`, `circ_444.json` | circulant colourings of K30 used by the positive controls |

**How to run** (from this folder):

    python3 check/verify_manifest.py certificates/manifest.json
    python3 check/check_flag5_mix.py certificates/R344_73.json                     # one certificate, base inputs
    python3 check/check_flag5_mix.py certificates/R355_316.json --input 3,4,4:73 --input 3,4,5:137
    python3 check/check_flag5_mix.py certificates/R355_316_r344le77.json --input 3,4,5:137   # the variant, no R(3,4,4) <= 73
    python3 check/controls_manifest.py certificates/manifest.json
    python3 check/controls_flag5.py && python3 check/controls_flag5_333.py && python3 check/controls_flag5_444.py && python3 check/controls_flag5_tk.py

**Expected output.** One block per entry, for example

    R(3, 4, 4) <= 73 [U] by R344_73.json (5-vertex); inputs: base only
    .../R344_73.json: t=(3, 4, 4) n=73 D=(17, 29, 29); 10 admissible profiles; ...; min Sym F - max J = 2.1769032980440205e-05 -> VALID

ending with `MANIFEST VERIFIED`. The margins (min Sym F - max J) run from 2.2e-5 (R(3,4,4) <= 73) down to
8.4e-9 (R(3,5,6) <= 619). The controls end with `ALL CONTROLS PASSED`.

The variant on its own (the command above) prints

      Ramsey inputs looked up: R(3, 4)<=9, R(3, 5)<=14, R(4, 4)<=18, R(4, 5)<=25, R(5, 5)<=46, R(3, 3, 4)<=30, R(3, 3, 5)<=57, R(3, 4, 4)<=77, R(3, 4, 5)<=137 [input]
    certificates/R355_316_r344le77.json: t=(3, 5, 5) n=316 D=(45, 136, 136); 6 admissible profiles; 81 stars, 180 rows, 93 squares in 8 blocks; 43166 valid labelled 5-patterns in 287 orbits; min Sym F - max J = 1.4675017507229086e-07 -> VALID
    ALL VALID

The first line shows that R(3,4,4) enters only as the base value 77 (no `[input]` tag). `R355_316.json` with
both inputs prints the same margin. Given the input R(3,4,4) <= 73, the variant is rejected (an assertion
`constant mismatch` on its row 34, recomputed as 72), and so is `R355_316.json` without it (recomputed as 76).

**Runtime** (10-core laptop, under load): `verify_manifest.py` 3 to 5 min (10 to 20 s per certificate; the
variant 10 s). `controls_manifest.py` makes about 9 checker runs per certificate, about 30 min in all. The
positive controls take about 8 min.
