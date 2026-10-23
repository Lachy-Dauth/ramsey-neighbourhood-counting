#!/bin/sh
# Re-run the computational checks of the paper (Python 3 standard library and a C++17 compiler).
#
#   sh run_all.sh             quick mode: every check that finishes in a few minutes (about 4 minutes in total)
#   sh run_all.sh --full      quick mode plus the long certificate checks and the direct clique searches
#                             (about 1.5 to 2 hours on a 10-core laptop; the last step alone takes about 50 min)
#   sh run_all.sh --controls  the expensive negative and positive controls of the flag certificates (about 2 hours)
#
# Works from any directory and exits non-zero as soon as a check fails.  Compiler: $CXX (default c++);
# Python: $PYTHON (default python3).  Build products and regenerated matrices are (in the git repository) git-ignored
# (make clean).  Runtimes are listed in README.md.
cd "$(dirname "$0")" || exit 2
MODE=quick
case "${1:-}" in
  "") ;;
  --full) MODE=full ;;
  --controls) MODE=controls ;;
  *) echo "usage: sh run_all.sh [--full | --controls]"; exit 2 ;;
esac
PY=${PYTHON:-python3}
CXX=${CXX:-c++}
export CXX
export PYTHONDONTWRITEBYTECODE=1    # keep the tree free of __pycache__
T0=$(date +%s)

run() { # run <label> <command ...>: run from this directory, stop at the first failure, report the wall time
  label=$1; shift
  echo "== $label"
  s=$(date +%s)
  if "$@"; then
    echo "   [ok, $(( $(date +%s) - s )) s]"
  else
    echo "FAILED: $label"
    echo "run_all.sh: FAILURE after $(( $(date +%s) - T0 )) s"
    exit 1
  fi
}
tail_of() { # tail_of <lines> <command ...>: run, print only the last lines of the output, keep the exit status
  n=$1; shift
  out=$("$@" 2>&1); rc=$?
  echo "$out" | tail -n "$n"
  return $rc
}
grep_of() { # grep_of <regex> <command ...>: run, print only the matching lines of the output, keep the exit status
  re=$1; shift
  out=$("$@" 2>&1); rc=$?
  if [ $rc -eq 0 ]; then echo "$out" | grep -E "$re"; else echo "$out" | tail -n 20; fi
  return $rc
}
in_dir() { # in_dir <dir> <command ...>
  ( d=$1; shift; cd "$d" && "$@" )
}
has_numpy() { $PY -c 'import numpy' >/dev/null 2>&1; }

quick() {
  # --- the original checks of the paper
  run "verify_hand_proofs.py: the main numerical steps of the hand proofs (Sections 4, 6)" $PY verify_hand_proofs.py
  run "verify_bootstrap.py: the ladder certificate tables.json (Theorem 5.2)" \
      grep_of '"(status|density_rows|degree_cases)"' $PY verify_bootstrap.py
  run "verify_cascade.py: R(3,4,7) <= 456, R(3,4,8) <= 700, R(3,5,6) <= 683 (Proposition 6.5)" \
      grep_of '"bound"' $PY verify_cascade.py
  run "verify_cascade_published_only.py: the same with published two-colour inputs only" \
      tail_of 1 $PY verify_cascade_published_only.py
  run "verify_r444.py: identities (I)-(III), R(4,4,4) <= 226 and <= 225 (Section 7)" tail_of 2 $PY verify_r444.py
  run "verify_r444_squares.py: R(4,4,4) <= 224, ..., 219 (four-vertex multi-square certificates)" \
      $PY verify_r444_squares.py
  run "check_circulants.py: the five circulant witnesses R(3,3,k) > n, (k,n) = (9,132), (11,182), (12,202), (13,231), (14,266)" \
      $PY check_circulants.py
  # --- new certificates
  run "flag5_r444: R(4,4,4) <= 204 (five-vertex certificate, check5.py)" \
      in_dir flag5_r444 $PY checkers/check5.py certificates/cert5_204.txt
  run "flag5_r444: the expansion used for the 'eloc' squares (identity check)" \
      in_dir flag5_r444 $PY controls/identity_eloc.py
  run "flag_r33k: R(3,3,6) <= 86, R(3,3,7) <= 125, R(3,3,8) <= 174 (standalone five-vertex exclusions)" \
      in_dir flag_r33k tail_of 4 $PY check_r33k5.py certificates/five/k6/excl_86.json \
      certificates/five/k7/excl_125.json certificates/five/k8/excl_174.json
  run "extension_r3315: R(3,3,15) >= 278 (rebuild the witness, certcheck)" sh extension_r3315/check_all.sh
}

full() {
  run "flag5_r444: R(4,4,4) <= 199 and R(4,4,4) <= 198 (five-vertex certificates, check5.py)" \
      in_dir flag5_r444 $PY checkers/check5.py certificates/cert5x_199.txt certificates/cert5x_198.txt
  if has_numpy; then
    run "flag5_r444: R(4,4,4) <= 198 again, independent checker over six-vertex orbits (check6.py, numpy)" \
        in_dir flag5_r444 $PY checkers/check6.py certificates/cert5x_198.txt
  else
    echo "== SKIPPED: flag5_r444/checkers/check6.py (second, independent checker for 198) needs numpy, not installed"
  fi
  run "flag5_r34k: R(3,4,4) <= 73, R(3,4,5) <= 137, R(4,4,4) <= 200, R(3,5,5) <= 316 (also without R(3,4,4) <= 73: R355_316_r344le77.json), R(3,4,6..8), R(3,5,6) (manifest)" \
      $PY flag5_r34k/check/verify_manifest.py flag5_r34k/certificates/manifest.json
  run "flag_r33k: the unified flag ladder, R(3,3,k) <= 86, 125, 173, 241, 309, 401, 505, 620, 748, 892 (k = 6..15)" \
      $PY flag_r33k/check_unified.py flag_r33k/certificates/unified/chain_final.json
  run "extension_r3315: R(3,3,15) >= 278, direct clique searches (kcheck, glue_check) and controls" \
      sh extension_r3315/check_all.sh --full
  run "compile check_colouring_full.cpp" $CXX -O3 -std=c++17 -o check_colouring_full check_colouring_full.cpp
  for w in "9 132" "11 182" "12 202" "13 231" "14 266"; do
    set -- $w
    run "check_colouring_full: direct clique search of R_3_3_$1_n$2.txt (no symmetry used)" \
        ./check_colouring_full R_3_3_$1_n$2.txt 3 3 $1
  done
  run "check_colouring_full: direct clique search of the 277-vertex R(3,3,15) witness (about 50 min)" \
      ./check_colouring_full extension_r3315/build/R_3_3_15_n277.txt 3 3 15
}

controls() {
  run "flag5_r444: negative controls on cert5x_198 (10 perturbed certificates must be rejected)" \
      in_dir flag5_r444 $PY controls/negative5.py certificates/cert5x_198.txt --extra-n=197 --extra-n=196
  run "flag5_r444: boundary control, cert5x_198 reused at n = 197" \
      in_dir flag5_r444 $PY controls/reuse5.py certificates/cert5x_198.txt 197
  if has_numpy; then
    run "flag5_r444: negative controls for check6.py (numpy)" \
        in_dir flag5_r444 $PY controls/negative6.py certificates/cert5x_198.txt
  else
    echo "== SKIPPED: flag5_r444/controls/negative6.py needs numpy, not installed"
  fi
  run "flag5_r34k: positive controls of check_flag5_mix.py on explicit colourings" sh -c \
      "$PY flag5_r34k/check/controls_flag5.py && $PY flag5_r34k/check/controls_flag5_333.py && $PY flag5_r34k/check/controls_flag5_444.py && $PY flag5_r34k/check/controls_flag5_tk.py"
  run "flag5_r34k: negative controls on every certificate of the manifest" \
      $PY flag5_r34k/check/controls_manifest.py flag5_r34k/certificates/manifest.json
  run "flag_r33k: soundness test of the five-vertex formulas on a real colouring (sanity5.py)" \
      in_dir flag_r33k $PY sanity5.py
  run "flag_r33k: negative controls for five-vertex certificates (controls5.py)" \
      in_dir flag_r33k $PY controls5.py certificates/unified/chain_final.json certificates/five/k6/excl_86.json \
      certificates/five/k7/excl_125.json certificates/five/k7/dens_120.json certificates/five/k8/excl_174.json
  run "flag_r33k: controls of the unified chain (controls_unified.py)" in_dir flag_r33k $PY controls_unified.py
}

echo "run_all.sh: $MODE mode ($($PY --version 2>&1); $($CXX --version 2>/dev/null | head -n 1))"
case $MODE in
  quick) quick ;;
  full) quick; full ;;
  controls) controls ;;
esac
echo "run_all.sh: all $MODE checks passed in $(( $(date +%s) - T0 )) s"
