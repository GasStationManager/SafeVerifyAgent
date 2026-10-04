#!/usr/bin/env bash
# Export the four GapCVP headline theorems and replay with every checker available.
set -u
cd /home/user/ten-proofs
export PATH=$HOME/.elan/bin:$PATH
O=/tmp/claude-0/-home-user/69126eca-8d7d-5969-ab6e-745654c8c3a5/scratchpad/gapcvp/export; mkdir -p $O
B32=$HOME/.elan/toolchains/leanprover--lean4---v4.32.0/bin
B35=$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin
EXP=.lake/packages/lean4export/.lake/build/bin/lean4export
TARGETS="Quot Quot.mk Quot.lift Quot.ind propext Quot.sound Classical.choice Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam"
DECLS="GapCVP.Comparator.gapCVP400IsNPHard GapCVP.Comparator.binaryNearestCodewordIsNPHard GapCVP.Comparator.binarySyndromeDecodingIsNPHard GapCVP.Comparator.finitePNormGapCVPIsNPHard"
echo "== export"; ( time lake env $EXP GapCVP -- $TARGETS $DECLS > $O/export.ndjson ) 2>&1 | grep real; ls -la $O/export.ndjson | awk '{print $5" bytes"}'; head -c 200 $O/export.ndjson; echo
echo "== leanchecker (v4.32.0)"; ( time $B32/leanchecker --from-export $O/export.ndjson > $O/leanchecker.log 2>&1; echo rc=$? ) 2>&1 | grep -E 'rc=|real'; tail -2 $O/leanchecker.log
for c in con-leche con-ron; do echo "== $c (v4.35.0-rc2 binary)"; ( time $B35/$c $( [ $c = con-leche ] && echo --verified ) $O/export.ndjson > $O/$c.log 2>&1; echo rc=$? ) 2>&1 | grep -E 'rc=|real'; tail -2 $O/$c.log; done
echo "{\"use_stdin\":false,\"export_file_path\":\"$O/export.ndjson\",\"permitted_axioms\":[\"propext\",\"Quot.sound\",\"Classical.choice\"],\"unpermitted_axiom_hard_error\":false,\"num_threads\":4,\"nat_extension\":true,\"string_extension\":true}" > $O/nanoda.json
echo "== nanoda (v4.35.0-rc2 binary)"; ( time $B35/nanoda_bin $O/nanoda.json > $O/nanoda.log 2>&1; echo rc=$? ) 2>&1 | grep -E 'rc=|real'; tail -2 $O/nanoda.log
