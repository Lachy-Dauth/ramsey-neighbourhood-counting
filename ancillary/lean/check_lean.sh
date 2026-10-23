#!/bin/sh
# Builds the Lean formalisation and checks it for unproved steps.
#
#   sh check_lean.sh        (from any directory)
#
# Needs elan (https://github.com/leanprover/elan), which provides `lake` and installs the
# toolchain named in lean-toolchain, and git and curl. The first run clones Mathlib and its
# dependencies at the revisions of lake-manifest.json and downloads the prebuilt Mathlib
# files with `lake exe cache get`; it never compiles Mathlib.
#
# Exit status 0 means: the build succeeded, Lean reported no `sorry`, every `#print axioms`
# line lists only propext, Classical.choice and Quot.sound, and no source file contains
# sorry, admit, native_decide or an `axiom` declaration.
set -u
cd "$(dirname "$0")" || exit 2

if ! command -v lake >/dev/null 2>&1; then
  echo "check_lean.sh: lake not found; install elan (https://github.com/leanprover/elan)" >&2
  exit 2
fi

echo "== lake exe cache get"
lake exe cache get || { echo "FAIL: lake exe cache get"; exit 1; }

echo "== lake build"
mkdir -p .lake
log=.lake/check_lean_build.log
{ lake build 2>&1; echo $? > .lake/check_lean_build.rc; } | tee "$log"
rc=$(cat .lake/check_lean_build.rc)
status=0
if [ "$rc" -ne 0 ]; then echo "FAIL: lake build exited with status $rc"; status=1; fi

echo "== checks"
if grep -qE "declaration uses 'sorry'|sorryAx" "$log"; then
  echo "FAIL: Lean reports sorry"; status=1
fi

# Messages may wrap over several lines, so join the log before extracting them.
ax=$(tr '\n' ' ' < "$log" | grep -oE "depends on axioms: \[[^]]*\]|does not depend on any axioms")
nax=$(printf '%s\n' "$ax" | grep -cE "axioms")
other=$(printf '%s\n' "$ax" | grep "depends on axioms" | sed -e 's/.*\[//' -e 's/\]//' | tr ',' '\n' |
  sed -e 's/^[[:space:]]*//' -e 's/[[:space:]]*$//' | grep -v -x -e '' -e propext \
  -e Classical.choice -e Quot.sound | sort -u)
if [ "$nax" -eq 0 ]; then
  echo "FAIL: no #print axioms output found in the build log"; status=1
elif [ -n "$other" ]; then
  echo "FAIL: axioms other than propext, Classical.choice, Quot.sound:"; echo "$other"; status=1
else
  echo "OK: $nax #print axioms results, all within [propext, Classical.choice, Quot.sound]"
fi

hits=$(grep -nE '(^|[^[:alnum:]_.])(sorry|admit|native_decide)([^[:alnum:]_]|$)' \
  RamseyLean.lean RamseyLean/*.lean)
if [ -n "$hits" ]; then
  echo "$hits"; echo "FAIL: sorry, admit or native_decide in the sources"; status=1
else
  echo "OK: no sorry, admit or native_decide in the sources"
fi
axdecl=$(grep -nE '^[[:space:]]*(@\[[^]]*\][[:space:]]*)?((private|protected|noncomputable|unsafe|partial)[[:space:]]+)*axiom[[:space:]]' \
  RamseyLean.lean RamseyLean/*.lean)
if [ -n "$axdecl" ]; then
  echo "$axdecl"; echo "FAIL: axiom declaration in the sources"; status=1
else
  echo "OK: no axiom declarations in the sources"
fi

if [ $status -eq 0 ]; then echo "check_lean.sh: all checks passed"; else echo "check_lean.sh: FAILED"; fi
exit $status
