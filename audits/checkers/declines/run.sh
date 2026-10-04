#!/usr/bin/env bash
# Export each fixture's theorem `t` and replay with four checkers; print one row per fixture.
cd "$(dirname "$0")"; export PATH=$HOME/.elan/bin:$PATH
EXP=/home/user/ten-proofs/.lake/packages/lean4export/.lake/build/bin/lean4export
B35=$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin
mkdir -p out
printf '%-14s %-28s %-28s %-28s %-28s\n' fixture leanchecker con-leche con-ron nanoda
for f in Fix/*.lean; do
  m=$(basename $f .lean); [ -f .lake/build/lib/lean/Fix/$m.olean ] || { printf '%-14s %s\n' $m "(did not build)"; continue; }
  if ! lake env $EXP Fix.$m -- t > out/$m.ndjson 2> out/$m.export.err; then printf '%-14s %s\n' $m "export failed: $(tail -c 120 out/$m.export.err | tr '\n' ' ')"; continue; fi
  v(){ # name cmd... -> "verdictword(rc)"
    local name=$1; shift; "$@" > out/$m.$name.log 2>&1; local rc=$?
    local msg=$(grep -oiE 'accept[a-z]* [0-9]* ?declarations|accepts the solution|declined[^.]{0,60}|rejected[^.]{0,60}|error[^.]{0,50}|unknown[^.]{0,50}' out/$m.$name.log | head -1 | cut -c1-26)
    printf '%s(rc %s)' "${msg:-?}" $rc; }
  echo "{\"use_stdin\":false,\"export_file_path\":\"$PWD/out/$m.ndjson\",\"permitted_axioms\":[\"propext\",\"Quot.sound\",\"Classical.choice\"],\"unpermitted_axiom_hard_error\":false,\"num_threads\":1,\"nat_extension\":true,\"string_extension\":true}" > out/$m.nanoda.json
  printf '%-14s %-28s %-28s %-28s %-28s\n' $m "$(v leanchecker $B35/leanchecker --from-export out/$m.ndjson)" "$(v conleche $B35/con-leche --verified out/$m.ndjson)" "$(v conron $B35/con-ron out/$m.ndjson)" "$(v nanoda $B35/nanoda_bin out/$m.nanoda.json)"
done
