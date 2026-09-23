#!/usr/bin/env bash
# Build the whole development, audit every paper statement, and write an
# immutable record of what was checked into BUILD_CERTIFICATE.txt.
#
# The certificate is a convenience record, not a proof: the trusted evidence is
# the Lean source together with the Lean kernel.  It states which commit, which
# toolchain and which dependency lockfile were used, and whether `lake build`
# and the statement/axiom audit succeeded.
#
# Usage:  ./scripts/build_certificate.sh   (from the repository root)

set -uo pipefail

cd "$(dirname "$0")/.."
OUT=BUILD_CERTIFICATE.txt

sha256() {
  if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | cut -d' ' -f1
  else shasum -a 256 "$1" | cut -d' ' -f1; fi
}

if ! git rev-parse --verify -q HEAD^{commit} >/dev/null 2>&1; then
  echo "error: this repository has no commit yet." >&2
  echo "The certificate binds the audit to a commit, and verify.py compares the" >&2
  echo "audited files against the committed tree.  Commit first, then re-run." >&2
  exit 2
fi

commit="$(git rev-parse HEAD)"
tree_state="clean"
# The certificate itself is written after the check and is not part of the tree it describes.
if [ -n "$(git status --porcelain 2>/dev/null | grep -v " ${OUT}$")" ]; then tree_state="dirty (uncommitted changes present)"; fi

lean_version="$(lean --version 2>/dev/null | head -1)"
lake_version="$(lake --version 2>/dev/null | head -1)"
toolchain="$(cat lean-toolchain)"
manifest_hash="$(sha256 lake-manifest.json)"
lakefile_hash="$(sha256 lakefile.lean)"

echo "== lake build All"
build_log="$(mktemp)"
lake build All 2>&1 | tee "$build_log"
build_status=${PIPESTATUS[0]}
# `lake build` succeeds on a file that still contains `sorry`; Lean only warns.
sorry_count="$(grep -c "declaration uses 'sorry'" "$build_log" || true)"
modules="$(ls ./*.lean | grep -cv lakefile.lean)"

echo "== axioms of every paper statement"
sweep=AxiomSweep.lean
{
  echo "import Overview_theorems"
  echo "import Theorems"
  for module in Overview_theorems Theorems; do
    namespace="$(grep -m1 '^namespace ' "$module.lean" | awk '{print $2}')"
    grep -oE "^(theorem|abbrev) [A-Za-z_][A-Za-z0-9_'.]*" "$module.lean" \
      | awk -v n="$namespace" '{print "#print axioms " n "." $2}'
  done
} > "$sweep"
statements="$(grep -c '^#print axioms' "$sweep")"
sweep_out="$(lake env lean "./$sweep" 2>&1)"
rm -f "$sweep"
reported="$(printf '%s\n' "$sweep_out" | grep -c 'depends on axioms\|does not depend on any axioms')"
used="$(printf '%s ' "$sweep_out" | grep -oE '\[[^]]*\]' | tr -d ' []' | tr ',' '\n' | sort -u | paste -sd' ')"
unexpected="$(printf '%s\n' "$sweep_out" | grep -oE '\[[^]]*\]' | tr -d ' []' | tr ',' '\n' \
  | grep -vE '^(propext|Classical\.choice|Quot\.sound)$' | sort -u | paste -sd' ')"

echo "== verify.py --manifest verification.json"
verify_out="$(python3 verify.py --manifest verification.json 2>&1)"
verify_status=$?
verified="$(printf '%s' "$verify_out" | grep -o '"verified": *[a-z]*' | head -1)"

{
  echo "BUILD CERTIFICATE"
  echo
  echo "This file records one complete check of the development.  It is not a"
  echo "cryptographic proof of correctness: the trusted evidence is the Lean"
  echo "source in this repository together with the Lean kernel.  What it fixes"
  echo "is exactly which source, toolchain and dependencies were checked."
  echo
  echo "date (UTC)             : $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "commit                 : ${commit}"
  echo "working tree           : ${tree_state}"
  echo "toolchain (lean-toolchain): ${toolchain}"
  echo "lean --version         : ${lean_version}"
  echo "lake --version         : ${lake_version}"
  echo "lake-manifest.json     : sha256 ${manifest_hash}"
  echo "lakefile.lean          : sha256 ${lakefile_hash}"
  echo
  echo "lake build All         : exit ${build_status}$( [ "$build_status" -eq 0 ] && echo '  (success)' )"
  echo "modules compiled       : ${modules} (the whole development; All.lean imports every one)"
  echo "'sorry' warnings       : ${sorry_count}"
  echo "paper statements       : ${reported} of ${statements} reported (Theorems.lean"
  echo "                         and Overview_theorems.lean)"
  echo "axioms used            : ${used}"
  echo "unexpected axioms      : ${unexpected:-none}"
  echo "verify.py              : exit ${verify_status}  ${verified}"
  echo
  echo "lake build All compiles every module of this repository, and Lean reports"
  echo "a remaining sorry only as a warning, which is why those are counted above."
  echo "The axiom sweep prints the transitive axiom dependencies of every paper"
  echo "statement; anything beyond propext, Classical.choice and Quot.sound -- in"
  echo "particular sorryAx and Lean.ofReduceBool -- is listed as unexpected.  The"
  echo "audit additionally elaborates the five contribution theorems against the"
  echo "exact statements recorded in verification.json, so a proof of a weaker"
  echo "statement cannot pass."
  echo
  echo "Reproduce with:"
  echo "    ./scripts/build_certificate.sh"
} > "$OUT"

echo
cat "$OUT"
rm -f "$build_log"
[ "$build_status" -eq 0 ] && [ "$verify_status" -eq 0 ] \
  && [ "$sorry_count" -eq 0 ] && [ -z "$unexpected" ] && [ "$reported" -eq "$statements" ]
