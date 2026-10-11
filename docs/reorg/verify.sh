#!/usr/bin/env bash
# Verify one reorganization step from a clean build.
#   docs/reorg/verify.sh BASELINE_DIR [BASE_REV]
# BASELINE_DIR holds inv.json (scripts/inventory.py snapshot) and check.log
# (`make check` output) of the baseline.  With BASE_REV, also check that every
# file renamed since BASE_REV has the same body once Requires are removed.
set -euo pipefail
B=$1; REV=${2:-}
cd "$(dirname "$0")/../../Code"
OUT=$(mktemp -d)

# Stale .vo files would satisfy a Require that still names an old path.
find . \( -name '*.vo' -o -name '*.vos' -o -name '*.vok' -o -name '*.glob' -o -name '.*.aux' \) \
  -not -path './Backup/*' -not -path './ITreeExamples/*' -delete
start=$(date +%s)
make -j8 > "$OUT/build.log" 2>&1 || { tail -30 "$OUT/build.log"; echo "BUILD FAILED"; exit 1; }
echo "build: ok ($(( $(date +%s) - start ))s)"

make check 2>&1 | grep -vE '^(make|COQ|coq_makefile|rm )|PaperClaims' > "$OUT/check.log" || { echo "CHECK FAILED"; exit 1; }
strip() { sed -E 's/Incorrectness(\.[A-Za-z0-9_]+)*\.//g' "$1"; }
if diff <(strip "$B/check.log") <(strip "$OUT/check.log") > "$OUT/check.diff"; then
  echo "make check: same assumptions"
else
  echo "make check: DIFFERENT"; head -20 "$OUT/check.diff"; exit 1
fi

python3 scripts/inventory.py snapshot "$OUT/inv.json" > /dev/null
python3 scripts/inventory.py compare "$B/inv.json" "$OUT/inv.json" | grep -v '^  moved'

python3 scripts/depgraph.py --check-layers 2>/dev/null | tail -1 || true

if [ -n "$REV" ]; then
  python3 ../docs/reorg/bodies.py "$REV" > "$OUT/bodies.log" || { grep 'BODY CHANGED' "$OUT/bodies.log"; exit 1; }
  echo "renamed files: $(grep -c "^same" "$OUT/bodies.log") unchanged, $(grep -c "^comments only" "$OUT/bodies.log") with comment edits ($(grep "^comments only" "$OUT/bodies.log" | sed "s/.* -> //" | tr "\n" " "))"
fi
echo "VERIFY OK ($OUT)"
