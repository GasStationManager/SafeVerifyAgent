#!/usr/bin/env bash
# E-A4 test: the NavierStokes library builds WITHOUT `autoImplicit := false`.
# lakefile.toml gives Euler `leanOptions = { autoImplicit = false, warningAsError = true }`
# and gives NavierStokes (816 files) and ComparatorChallenges NOTHING.
# A mistyped identifier in a STATEMENT is then silently auto-bound as a fresh implicit
# rather than erroring, which cannot prove a false theorem (auto-binding generalises)
# but can leave an intermediate lemma quietly about a fresh variable.
#
# Non-invasive by construction: we do NOT edit lakefile.toml. Each file is re-elaborated
# with the flags supplied on the command line, against the already-built .olean deps.
set -uo pipefail
cd /home/gsm/.openclaw/workspace/repos/NSE
OUT="$1"; shift
: > "$OUT"
for f in "$@"; do
  # timeout generously; record only the verdict line plus any autoImplicit-attributable error
  err=$(timeout 900 lake env lean -DautoImplicit=false -DwarningAsError=true "$f" 2>&1)
  rc=$?
  if [ $rc -eq 0 ]; then
    echo "PASS  $f" >> "$OUT"
  else
    n=$(printf '%s\n' "$err" | grep -c "error:")
    echo "FAIL  $f  (rc=$rc, errors=$n)" >> "$OUT"
    printf '%s\n' "$err" | grep -m6 "error:" | sed 's/^/        /' >> "$OUT"
  fi
done
echo "=== done $(date -u) ===" >> "$OUT"
