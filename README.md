# Neighbourhood counting and new bounds for small Ramsey numbers

This repository has two papers on small Ramsey numbers, and the certificates and exact checkers for every
computer-assisted claim in them. Run `make verify` to re-check the quick part in a few minutes.

- **[A] Neighbourhood counting and new bounds for small three-colour Ramsey numbers** ([pdf](paper/neighbourhood_counting.pdf), [tex](paper/neighbourhood_counting.tex))
- **[B] New bounds for small two-colour Ramsey numbers** ([pdf](paper/two_colour.pdf), [tex](paper/two_colour.tex))

> **Status.** These are preprints, not yet peer reviewed. The hand proofs can be checked with pen and paper.
> The other results are computer-assisted. Every certificate and witness is verified in exact arithmetic by
> programs in [`ancillary/`](ancillary/), which share no code with the searches that found them.
> Please report any problem as an issue.

## Results

Three colours (paper A). The previous values are from Radziszowski's survey (DS1, revision 18) and Boza (2026).

| number | previous upper bound | by hand | by computer |
|---|---|---|---|
| R(4,4,4) | 229 | 226 | **198** |
| R(3,4,4) | 77 | | **73** |
| R(3,4,5) | 157 | 155 | **137** |
| R(3,3,6) | 91 | 88 | **86** |
| R(3,3,7) | (136 from the recurrence) | 129 | **125** |
| R(3,3,8) | (191 from the recurrence) | 179 | **173** |
| R(3,3,k), 9 <= k <= 15 | (261 ... 1019 from the recurrence) | | **241, 309, 401, 505, 620, 748, 892** |
| R(3,5,5) | (359) | 346 | **316** |
| R(3,4,6) | (288) | 276 | **247** |
| R(3,4,7), R(3,4,8), R(3,5,6) | (483, 757, 733) | 458, 705, 685 | **409, 626, 622** |

For 9 <= k <= 15, the ladder of A, Theorem 5.2 (computer-assisted, without flag certificates) gives
R(3,3,k) <= 247, 315, 407, 512, 628, 756, 901; the bold values use the flag certificates of A, Theorem 8.5.

Every value in this table uses published inputs only. With the two-colour bounds that the survey reports as
unpublished (A, Table 3), the benchmarks become 287 for R(3,4,6) and 479, 748, 730 for the last row, the hand
bounds in the last row 456, 700, 683, and the computer bounds R(3,4,6) <= 245 and 406, 625, 619 (A, Table 1).

| number | previous lower bound | new |
|---|---|---|
| R(3,3,9), R(3,3,11), R(3,3,12) | 129, 174, 194 | **133, 183, 203** |
| R(3,3,13), R(3,3,14), R(3,3,15) | 217, 242, 269 | **232, 267, 278** |

Four colours (paper A, Corollary 8.7): from R(3,4,4) <= 73 and R(4,4,4) <= 198, by the four-colour
neighbourhood recurrence with the survey's R(3,3,3,4) <= 149.

| number | previous upper bound | new |
|---|---|---|
| R(3,3,4,4), R(3,4,4,4), R(4,4,4,4) | 450, 1576, 6306 (6301 implicit in Boza 2026) | **442, 1521, 6082** |

Two colours (paper B):

| number | previous | new |
|---|---|---|
| R(3,k), 24 <= k <= 50 | no upper bound listed | **R(3,24) <= 201, ..., R(3,50) <= 729** |
| R(4,21) | >= 242 (257 implied by a 2026 preprint) | **>= 260** |
| R(4,24) | >= 343 (implicit) | **>= 370** |

The main new tool is the flag-algebra certificate (Razborov) whose constraints include *local caps*. A local cap
bounds an intersection of colour neighbourhoods by a smaller Ramsey number. Without the caps, flag algebras give
only 85 for R(3,4,4) (Lidický and Pfender). See paper A, Section 8.

## Checking the results

Requirements: Python 3 (standard library), a C++17 compiler and a C compiler with POSIX threads. NumPy is optional;
it is used only by one second checker and its negative controls.

```sh
make verify            # quick mode, a few minutes (this is what CI runs)
make verify-full       # also the long certificate checks and direct clique searches (1.5-2 hours)
make verify-controls   # negative and positive controls of the certificates (about 2 hours)
make paper             # rebuild both PDFs (needs pdflatex)
```

[`ancillary/README.md`](ancillary/README.md) lists every file, the result it checks, its mode and its runtime.
Each subfolder has its own README, with the inputs it assumes and the expected output.

| folder | checks |
|---|---|
| `ancillary/` (top level) | hand-proof arithmetic, the ladder certificate, the four-vertex R(4,4,4) identities, the circulant witnesses (A, Sections 3-7 and 9) |
| `ancillary/flag5_r444/` | R(4,4,4) <= 198 (A, Theorem 8.2) |
| `ancillary/flag5_r34k/` | R(3,4,4) <= 73, R(3,4,5) <= 137 and the chain to R(3,4,8) (A, Theorem 8.3) |
| `ancillary/flag_r33k/` | R(3,3,k) for 6 <= k <= 15 (A, Theorems 8.4, 8.5) |
| `ancillary/extension_r3315/` | R(3,3,15) >= 278 (A, Theorem 9.3) |
| `ancillary/two_colour_r3k/` | R(3,k) for k <= 50 (B, Theorem 2.1) |
| `ancillary/two_colour_r4k/` | R(4,21) >= 260, R(4,24) >= 370 (B, Theorem 3.1) |
| `ancillary/lean/` | Lean 4 proofs of two facts used in Lemma 3.1 of A (described in A, Section 10; needs Mathlib) |

The checkers verify the finite computations that the proofs reduce to. Published Ramsey values used as inputs are
premises; each README lists them. Some inputs are themselves computer results, for example R(3,3,4) = 30.

## How the work was done

The research, proofs, programs and papers were produced by Lachlan Dauth working with two AI systems: OpenAI's
Codex (based on GPT-6) in the first stage of the project, and Claude Opus 5.5, a large language model developed by
Anthropic, in the later stages. In line with arXiv's policy, the models are acknowledged in the papers rather
than listed as an author. Certificates were found with floating-point solvers and local search, then rounded and
checked exactly. Each result was also re-checked, before inclusion, by a separately written exact verifier that
shares no code with the search (both were written with these AI systems; see the Acknowledgements of the papers).

## Licence

The code and data are under the MIT licence (see `LICENSE`). The paper texts are copyright the author.

## Citation

See `CITATION.cff`, or cite the papers as:

> L. Dauth, *Neighbourhood counting and new bounds for small three-colour Ramsey numbers*, preprint, 2026.
> L. Dauth, *New bounds for small two-colour Ramsey numbers*, preprint, 2026.
