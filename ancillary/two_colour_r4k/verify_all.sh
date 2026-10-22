#!/bin/sh
# verify_all.sh : rebuild and exactly check the two-colour lower bounds R(4,21) >= 260 and R(4,24) >= 370.
# Usage: sh verify_all.sh [--full] [threads]
#   default : rebuild both graphs from the deletion lists (SHA-256 against the recorded hashes), the complete
#             checks (rcheck for the 259-vertex graph; K4-freeness by rcheck and alpha <= 23 by qpsym for the
#             369-vertex graph) and the negative controls.
#   --full  : also the direct rcheck of the 369-vertex graph for independent 24-sets (about 10 min on 10 threads;
#             qpsym is already a complete check of alpha <= 23).
# Needs a C compiler (cc, or $CC) with POSIX threads, and python3.  Build products go to build/ (git-ignored).
set -u
FULL=0; T=""
for a in "$@"; do case $a in --full) FULL=1 ;; *) T=$a ;; esac; done
[ -n "$T" ] || T=$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 2)
cd "$(dirname "$0")"
mkdir -p build
CC=${CC:-cc}
$CC -O3 -pthread -o build/rcheck rcheck.c && $CC -O3 -pthread -o build/qpsym qpsym.c || { echo "BUILD FAILED"; exit 2; }
RC=build/rcheck; QP=build/qpsym
ok=1
sha() { python3 -c 'import hashlib, sys; print(hashlib.sha256(open(sys.argv[1], "rb").read()).hexdigest())' "$1"; }
expect() { # expect <PASS|FAIL|ALLHIT|NOTHIT> <cmd...>
  want=$1; shift
  out=$("$@" 2>&1); last=$(echo "$out" | tail -1)
  case $want in
    PASS) echo "$last" | grep -q '^PASS' ;;
    FAIL) echo "$last" | grep -q '^FAIL' ;;
    ALLHIT) echo "$last" | grep -q '^ALL HIT' ;;
    NOTHIT) echo "$out" | grep -q '^NOT HIT' && ! echo "$out" | grep -q 'VERIFY FAILED' ;;
  esac
  if [ $? -eq 0 ]; then echo "ok   [$want] $*   | $last"; else echo "BAD  [$want] $*"; echo "$out" | tail -3; ok=0; fi
}
rebuild() { # rebuild <p> <deletion list> <out> <expected sha256>
  python3 build_power_sub.py "$1" 4 "$2" "$3" >/dev/null || { echo "BAD  rebuild $3"; ok=0; return; }
  h=$(sha "$3")
  if [ "$h" = "$4" ]; then echo "ok   rebuilt $3 (Q$1 minus $2), sha256 $h"; else echo "BAD  $3 sha256 $h, expected $4"; ok=0; fi
}
echo "== R(4,21) >= 260: Q313 minus 54 vertices (259 vertices)"
rebuild 313 certs/R_4_21_n259_deleted_from_Q313.txt build/R_4_21_n259.txt d8e985da486f9398497342bfaa0185cf31ececb436719a51c7e9205822a5de81
expect PASS   $RC build/R_4_21_n259.txt 4 21 $T                               # no K4, no independent 21-set
expect ALLHIT $QP 313 4 21 certs/R_4_21_n259_deleted_from_Q313.txt $T         # second check: alpha(Q313 - S) <= 20
expect FAIL   $RC build/R_4_21_n259.txt 4 20 1 stopfail                       # control: it has independent 20-sets
expect FAIL   $RC build/R_4_21_n259.txt 3 21 1 stopfail                       # control: it has triangles
python3 -c "import sys; S = open(sys.argv[1]).read().split(); S.pop(0); open(sys.argv[2], 'w').write(' '.join(S))" certs/R_4_21_n259_deleted_from_Q313.txt build/ctl313.txt
expect NOTHIT $QP 313 4 21 build/ctl313.txt $T                                # control: one deleted vertex restored
expect NOTHIT $QP 313 4 21 - $T                                               # control: alpha(Q313) >= 21
expect ALLHIT $QP 313 4 22 - $T                                               # alpha(Q313) <= 21
echo "== R(4,24) >= 370: Q457 minus 88 vertices (369 vertices)"
rebuild 457 certs/R_4_24_n369_deleted_from_Q457.txt build/R_4_24_n369.txt bdc972d8b3fbf5295e7155806a69ffaf2792d5ad21cc53ea6720004d6e651a8b
expect PASS   $RC build/R_4_24_n369.txt 4 400 $T                              # no K4 (the independent-set part is trivial here)
expect ALLHIT $QP 457 4 24 certs/R_4_24_n369_deleted_from_Q457.txt $T         # alpha(Q457 - S) <= 23
expect FAIL   $RC build/R_4_24_n369.txt 4 23 1 stopfail                       # control: it has independent 23-sets
expect FAIL   $RC build/R_4_24_n369.txt 3 24 1 stopfail                       # control: it has triangles
python3 -c "import sys; S = open(sys.argv[1]).read().split(); S.remove('213'); open(sys.argv[2], 'w').write(' '.join(S))" certs/R_4_24_n369_deleted_from_Q457.txt build/ctl457.txt
expect NOTHIT $QP 457 4 24 build/ctl457.txt $T                                # control: vertex 213 restored
if [ $FULL = 1 ]; then
  echo "== direct check of the 369-vertex graph (long)"
  expect PASS $RC build/R_4_24_n369.txt 4 24 $T
fi
if [ $ok = 1 ]; then echo "ALL CHECKS AS EXPECTED"; exit 0; else echo "SOME CHECK FAILED"; exit 1; fi
