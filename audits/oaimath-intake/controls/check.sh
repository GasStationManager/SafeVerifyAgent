#!/usr/bin/env bash
# Export a built openai/math solution module's headline theorem and replay with every checker.
# usage: check.sh <Name> <Module> <Decl...>
set -u
NAME=$1; MOD=$2; shift 2; DECLS="$*"
cd /home/user/openai-math/repo/lean
export PATH=$HOME/.elan/bin:$PATH
S=<scratch>/oaimath
O=$S/export/out/$NAME; mkdir -p $O
B34=$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin
B35=$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin
EXP=$S/export/lean4export/.lake/build/bin/lean4export
TARGETS="Quot Quot.mk Quot.lift Quot.ind propext Quot.sound Classical.choice Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.blt Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight Nat.log2 String.ofList Char.ofNat List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam"
echo "== export $MOD :: $DECLS"
( TIMEFORMAT='real %Rs'; time lake env $EXP $MOD -- $TARGETS $DECLS > $O/export.ndjson ) 2>&1 | tail -1
ls -la $O/export.ndjson | awk '{print $5" bytes"}'; wc -l < $O/export.ndjson | sed 's/^/lines /'
echo "== leanchecker (v4.35.0-rc2)"; ( TIMEFORMAT='real %Rs'; time $B35/leanchecker --from-export $O/export.ndjson > $O/leanchecker35.log 2>&1; echo rc=$? ) 2>&1 | tail -2; tail -2 $O/leanchecker35.log
for c in con-leche con-ron; do echo "== $c (v4.35.0-rc2 binary)"; ( TIMEFORMAT='real %Rs'; time $B35/$c $( [ $c = con-leche ] && echo --verified ) $O/export.ndjson > $O/$c.log 2>&1; echo rc=$? ) 2>&1 | tail -2; tail -3 $O/$c.log; done
echo "{\"use_stdin\":false,\"export_file_path\":\"$O/export.ndjson\",\"permitted_axioms\":[\"propext\",\"Quot.sound\",\"Classical.choice\"],\"unpermitted_axiom_hard_error\":false,\"num_threads\":4,\"nat_extension\":true,\"string_extension\":true}" > $O/nanoda.json
echo "== nanoda (v4.35.0-rc2 binary)"; ( TIMEFORMAT='real %Rs'; time $B35/nanoda_bin $O/nanoda.json > $O/nanoda.log 2>&1; echo rc=$? ) 2>&1 | tail -2; tail -2 $O/nanoda.log
