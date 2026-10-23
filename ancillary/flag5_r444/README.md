# flag5_r444: five-vertex flag certificates for R(4,4,4) <= 198

**What it proves.** R(4,4,4) <= 198, and also <= 199 and <= 204 from separate certificates. Each certificate is
an exact rational certificate on labelled colourings of K5. Its star coefficients, cap rows (one- to
four-rooted neighbourhood caps, plus lower degree bounds), and squares ('edge', 'tri', 'vpair' and the
edge-rooted localising squares 'eloc') add up to a function F. Every S5 x S3 orbit average of F is <= 0, while
the star part J(d) is > 0 at every admissible degree profile. So no (4,4,4;n)-colouring exists. The docstring
of `checkers/check5.py` gives every definition.

**Inputs assumed.** These are published values, and the checker recomputes every cap constant from them:
R(3,4,4) <= 77 (the survey value, Radziszowski DS1.18), R(3,3,4) = 30, R(3,3,3) = 17, R(4,4) = 18, R(3,4) = 9,
R(3,3) = 6, R(2,k) = k. So every colour degree is at most 76. The R(3,4,4) <= 73 of `../flag5_r34k` is *not*
used. With `--r344=K` the checker uses the hypothesis R(3,4,4) <= K instead.

| file | contents |
|---|---|
| `certificates/cert5x_198.txt` | R(4,4,4) <= 198: 1581 caps, 233 squares (120 of them 'eloc') |
| `certificates/cert5x_199.txt` | R(4,4,4) <= 199 (same model) |
| `certificates/cert5_204.txt` | R(4,4,4) <= 204 (base model, no 'eloc' squares; the quick check) |
| `checkers/check5.py` | exact checker over the 133 S5 x S3 orbits of K5 colourings without a monochromatic K4 (standard library) |
| `checkers/check6.py` | second, independent exact checker that works in the 3929 S6 x S3 orbits of K6 colourings (**needs numpy**) |
| `controls/negative5.py` | 10 perturbed copies of a certificate (eloc and cap constants off by one, a negated multiplier, star coefficients +-1e-5, no squares, n lowered to 197 and 196), all of which must be rejected by check5 |
| `controls/reuse5.py` | boundary control: the 198 certificate reused at 197, with the n-dependent constants shifted, must be rejected |
| `controls/negative6.py` | 4 perturbed copies, all of which must be rejected by check6 (needs numpy) |
| `controls/identity_eloc.py` | brute-force check of the expansion used for the 'eloc' squares on a random colouring of K9 |

The certificates are plain text with exact rationals `p/q`. The format is in the docstring of `load_text` in
`check5.py`. They are the text export of the original pickled certificates, and the export was checked to be
lossless.

**How to run** (from this folder):

    python3 checkers/check5.py certificates/cert5x_198.txt     # R(4,4,4) <= 198
    python3 checkers/check5.py certificates/cert5x_199.txt certificates/cert5_204.txt
    python3 checkers/check6.py certificates/cert5x_198.txt     # optional second checker (numpy)
    python3 controls/negative5.py certificates/cert5x_198.txt --extra-n=197 --extra-n=196
    python3 controls/reuse5.py certificates/cert5x_198.txt 197
    python3 controls/negative6.py certificates/cert5x_198.txt  # numpy
    python3 controls/identity_eloc.py

**Expected output.**

    certificates/cert5x_198.txt: n=198; 1581 caps, 233 squares; 133 orbits without mono K4; max orbit-average of F = -3.050e-09 (<= 0 OK); 528 profiles, min J = 3.046e-09 (> 0 OK)
    certificates/cert5x_199.txt: n=199; ... max orbit-average of F = -9.958e-08 (<= 0 OK); 496 profiles, min J = 9.943e-08 (> 0 OK)
    certificates/cert5_204.txt: n=204; 1581 caps, 113 squares; ... F = -4.007e-07 (<= 0 OK); 351 profiles, min J = 4.006e-07 (> 0 OK)
    ALL VALID
    check6: certificates/cert5x_198.txt: n=198; 1581 caps, 233 squares in 17 groups; 3929 orbits without mono K4; max orbit-average of F = -3.050e-09 (<= 0 OK); 528 profiles, min J = 3.046e-09 (> 0 OK)
    negative5: ALL CONTROLS REJECTED (10 controls);  reuse5: control reuse at 197 : rejected;  negative6: ALL CONTROLS REJECTED;  identity_eloc: mismatches: 0

The margins are small (3e-9) but exact: every number is a Fraction.

**Runtime** (wall time on a 10-core laptop, under load): check5 about 2.5 min for 198 or 199, and 35 s for 204.
check6 about 7 min (and over 1 GB of memory). negative5 about 6 min, negative6 about 22 min, reuse5 about 4 min.
