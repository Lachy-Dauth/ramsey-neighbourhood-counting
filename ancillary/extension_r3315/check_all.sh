#!/bin/sh
# R(3,3,15) >= 278: exact checks of the 277-vertex witness.  Usage: sh check_all.sh [--full]
#   default : rebuild the matrix from the compact description (SHA-256), check that its host is the paper's
#             (3,3,14;266) circulant (green graph), certcheck.py (PASS for k = 15, control FAIL for k = 14).
#   --full  : also direct exact clique searches with kcheck.cpp (no red/blue K3, no green K15: about 1 minute),
#             glue_check.cpp (green clique number exactly 14: a few minutes), and the negative controls in
#             controls.py (kcheck -max: about 6 minutes).
# Needs python3 and, for --full, a C++ compiler (c++, or $CXX).  Build products go to build/ (git-ignored).
set -e
cd "$(dirname "$0")"
python3 check_277.py build
[ "${1:-}" = "--full" ] || exit 0
CXX=${CXX:-c++}
$CXX -O3 -std=c++17 -o build/kcheck kcheck.cpp
$CXX -O3 -std=c++17 -o build/glue_check glue_check.cpp
F=build/R_3_3_15_n277.txt
echo "== kcheck $F 3 3 15 (exit 0 iff no red K3, no blue K3, no green K15)"
./build/kcheck $F 3 3 15
echo "== glue_check $F 266 2 (green clique number, split as host + 11 new vertices)"
out=$(./build/glue_check $F 266 2); echo "$out"
echo "$out" | grep -q 'clique_number=14 ' || { echo "glue_check: green clique number is not 14"; exit 1; }
echo "== controls.py (kcheck -max 2 must give 14; a recoloured red K3 and green K15 must be found)"
out=$(python3 controls.py build/kcheck $F 15 build/ctl277); echo "$out"
[ "$(echo "$out" | grep -c ' PASS$')" -eq 3 ] || { echo "controls: not all three PASS"; exit 1; }
echo "R(3,3,15) >= 278: full checks passed"
