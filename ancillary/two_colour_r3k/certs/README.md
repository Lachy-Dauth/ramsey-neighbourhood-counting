# R(3,k) upper-bound certificates (two-colour front, 23 Oct 2026)

Files
- `r3k_pub_seq_k50.json`: inputs GR13 Tables 3-5 and Theorem 2, and R(3,10) <= 42 (GR13 Theorem 6). Bootstrap,
  plus exact degree-sequence enumeration, plus the transport LP. Angeltveit's R(3,10) <= 41 is not needed:
  without `--r310 42` the checker uses 41, with the same result.
- `r3k_back3_seq_k50.json`: as above, plus the lower bounds of Backelin's Edge number report 1
  (arXiv:1410.1843, Section 5 table, columns l = 10..13, n = 35..43), transcribed in
  `checker/cited_extra.txt`.

Check (exact, and independent of the generating programs, which are not part of this repository):

    python3 checker/check_r3k_v2.py --r310 42 certs/r3k_back3_seq_k50.json --claim 16,97 --claim 19,132 --claim 23,185
    python3 checker/check_r3k_v2.py --r310 42 certs/r3k_pub_seq_k50.json --no-back3 --claim 17,109 --claim 20,145
    python3 checker/negative_controls_v2.py certs/r3k_back3_seq_k50.json
    python3 checker/negative_controls_high.py certs/r3k_back3_seq_k50.json

Row types: see the docstrings of `checker/check_r3k.py` and `checker/check_r3k_v2.py`. A 'seq' row raises
m_k(n) from e0 to m by excluding every e in [e0, m). The checker enumerates all degree sequences that
satisfy the degree caps and the Graver-Yackel inequality (and d_v <= e - m_k(n-1)). For each one it requires
either a failing neighbour-count test or a Farkas certificate (named constraints, rational multipliers)
for the transport LP, which it rebuilds from the definitions.
