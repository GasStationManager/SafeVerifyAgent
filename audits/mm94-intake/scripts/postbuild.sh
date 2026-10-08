#!/usr/bin/env bash
# Wait for the route build, then axioms + export + checkers. Output: $O
set -u
S=<scratch>
O=$S/mm94/out; mkdir -p $O
cd /home/user/openai-math/repo/lean; export PATH=$HOME/.elan/bin:$PATH
until grep -q '^real ' $S/mm94build.log 2>/dev/null; do sleep 60; done
echo "== build log"; cat $S/mm94build.log
ls .lake/build/lib/lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Main.olean || { echo "NO OLEAN, abort"; exit 1; }
echo "== print axioms"; ( TIMEFORMAT='real %Rs'; time lake env lean $S/mm94/axioms.lean > $O/axioms.txt 2>&1 ) 2>&1 | tail -1; cat $O/axioms.txt
B35=$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin
EXP=$S/oaimath/export/lean4export/.lake/build/bin/lean4export
TARGETS="Quot Quot.mk Quot.lift Quot.ind propext Quot.sound Classical.choice Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.blt Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight Nat.log2"
DECLS="OAI.MatrixMultiplication.AuxiliarySeparation.omega_le_nine_quarters OAI.MatrixMultiplication.AuxiliarySeparation.matrix_multiplication_cost_le"
echo "== export"; ( TIMEFORMAT='real %Rs'; time lake env $EXP OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Main -- $TARGETS $DECLS > $O/export.ndjson 2>$O/export.err ) 2>&1 | tail -1
ls -la $O/export.ndjson | awk '{print $5" bytes"}'; wc -l < $O/export.ndjson | sed 's/^/lines /'
echo "sorryAx refs: $(grep -c '"str":"sorryAx"' $O/export.ndjson)"
python3 -I - <<'PY' > $O/cone-from-export.txt
import json,collections
names={}
for line in open('<scratch>/mm94/out/export.ndjson'):
    try: d=json.loads(line)
    except Exception: continue
    if 'in' in d: names[d['in']]=(d.get('p'),d.get('str'))
def full(i):
    out=[]
    while i and i in names:
        p,s=names[i]; out.append(str(s)); i=p
    return '.'.join(reversed(out))
decl=collections.Counter(); files=collections.Counter()
for line in open('<scratch>/mm94/out/export.ndjson'):
    try: d=json.loads(line)
    except Exception: continue
    for k in ('def','thm','ax','opaque','ind','quot'):
        if k in d:
            n=full(d[k].get('n')) if isinstance(d[k],dict) else ''
            if n.startswith('OAI.'): decl[k]+=1; files['.'.join(n.split('.')[:3])]+=1
print('OAI constants reached from the headline, by kind:',dict(decl))
for k,v in files.most_common(40): print(f'{v:6d} {k}')
PY
head -3 $O/cone-from-export.txt
echo "== leanchecker (v4.35.0-rc2)"; ( TIMEFORMAT='real %Rs'; time $B35/leanchecker --from-export $O/export.ndjson > $O/leanchecker.log 2>&1; echo rc=$? ) 2>&1 | tail -2; tail -2 $O/leanchecker.log
for c in con-leche con-ron; do echo "== $c"; ( TIMEFORMAT='real %Rs'; time $B35/$c $( [ $c = con-leche ] && echo --verified ) --jobs=3 $O/export.ndjson > $O/$c.log 2>&1; echo rc=$? ) 2>&1 | tail -2; tail -3 $O/$c.log; done
echo "{\"use_stdin\":false,\"export_file_path\":\"$O/export.ndjson\",\"permitted_axioms\":[\"propext\",\"Quot.sound\",\"Classical.choice\"],\"unpermitted_axiom_hard_error\":false,\"num_threads\":3,\"nat_extension\":true,\"string_extension\":true,\"declar_sep\":\"\\n\",\"print_success_message\":true}" > $O/nanoda.json
echo "== nanoda"; ( TIMEFORMAT='real %Rs'; time $B35/nanoda_bin $O/nanoda.json > $O/nanoda.log 2>&1; echo rc=$? ) 2>&1 | tail -2; tail -2 $O/nanoda.log
echo "== DONE"
