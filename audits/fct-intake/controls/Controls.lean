import FourColor.Reducibility.Cf001

/-! Positive and negative controls for the engine's trust claim, run against the
built certificate of cf001 (ring size 6). -/

open Lean Elab Command Meta FourColor FourColor.Engine FourColor.Engine.Gen

#print axioms FourColor.cf001_reducible
#check @FourColor.cf001_reducible

-- Positive control: re-add cf001_init under a new name with the SAME literal.
run_cmd liftCoreM do
  let rE := mkNatLit 6
  let sE := mkNatLit chunkLog
  let dpHE := mkNatLit dpChunkDigits
  let cnvE := mkConst ``FourColor.Engine.cnvNet6
  let cnvCE := mkConst ``FourColor.Engine.cnvNetC6
  let cfE := mkConst ``FourColor.cf001
  let cfprogE := mkApp (mkConst ``Config.cfprog) cfE
  let H0 := mkConst ``FourColor.cf001_H0
  let lhs := mkApp4 (mkConst ``checkInit) rE cnvE cfprogE H0
  let rhs := mkAppN (mkConst ``checkInitB) #[rE, sE, dpHE, cnvCE, cfprogE, H0]
  let eq := mkAppN (mkConst ``checkInit_eq_checkInitB) #[sE, cnvCE, mkConst ``FourColor.Engine.cnvNetOK6, rE, dpHE, cfprogE, H0]
  let pf := mkAppN (mkConst ``Eq.trans [1]) #[mkConst ``Bool, lhs, rhs, mkConst ``true, eq, reflTrue]
  addThm `Controls.init_same (mkEqTrue lhs) pf
  logInfo "positive control: accepted"

-- Negative control: the same theorem about a checkpoint with ONE bit flipped.
run_cmd liftCoreM do
  let v ← constValue ``FourColor.cf001_H0
  let some xs := listOfExpr? v | throwError "H0 is not a list literal"
  let ns ← xs.mapM fun e => do
    let some n := natOfExpr? e | throwError "not a nat"
    pure n
  -- flip the lowest bit of the last nonzero entry
  let i := (List.range ns.length).reverse.find? (fun i => ns[i]! != 0) |>.getD 0
  let ns' := ns.set i (ns[i]! ^^^ 1)
  logInfo m!"H0 has {ns.length} entries; flipping bit 0 of entry {i}"
  addDataDef `Controls.H0bad (mkApp (mkConst ``List [0]) (mkConst ``Nat)) (mkNatListLit ns')
  let rE := mkNatLit 6
  let sE := mkNatLit chunkLog
  let dpHE := mkNatLit dpChunkDigits
  let cnvE := mkConst ``FourColor.Engine.cnvNet6
  let cnvCE := mkConst ``FourColor.Engine.cnvNetC6
  let cfE := mkConst ``FourColor.cf001
  let cfprogE := mkApp (mkConst ``Config.cfprog) cfE
  let H0 := mkConst `Controls.H0bad
  let lhs := mkApp4 (mkConst ``checkInit) rE cnvE cfprogE H0
  let rhs := mkAppN (mkConst ``checkInitB) #[rE, sE, dpHE, cnvCE, cfprogE, H0]
  let eq := mkAppN (mkConst ``checkInit_eq_checkInitB) #[sE, cnvCE, mkConst ``FourColor.Engine.cnvNetOK6, rE, dpHE, cfprogE, H0]
  let pf := mkAppN (mkConst ``Eq.trans [1]) #[mkConst ``Bool, lhs, rhs, mkConst ``true, eq, reflTrue]
  try
    addThm `Controls.init_bad (mkEqTrue lhs) pf
    logError "NEGATIVE CONTROL FAILED: kernel accepted a flipped checkpoint"
  catch e =>
    logInfo m!"negative control: kernel rejected the flipped checkpoint: {e.toMessageData}"

-- Negative control 2: a wrong NETWORK literal (drop the last layer of tauNetC6) must fail netCOK/tauLayers/parts.
run_cmd liftCoreM do
  let v ← constValue ``FourColor.Engine.tauNetC6
  let some layers := listOfExpr? v | throwError "not a list"
  let nat := mkConst ``Nat
  let lnat := mkApp (mkConst ``List [0]) nat
  let pairTy := mkApp2 (mkConst ``Prod [0, 0]) lnat nat
  let bad := layers.dropLast.foldr (fun l acc => mkApp3 (mkConst ``List.cons [0]) pairTy l acc) (mkApp (mkConst ``List.nil [0]) pairTy)
  addDataDef `Controls.tauC_bad (mkConst ``NetC) bad
  addDataDef `Controls.tau_bad (mkConst ``Net) (mkApp2 (mkConst ``netOfChunks) (mkNatLit chunkLog) (mkConst `Controls.tauC_bad))
  let fE := mkApp2 (mkConst ``tauCheckAt) (mkNatLit 6) (mkConst `Controls.tau_bad)
  let mut rejected : Nat := 0
  for p in [0:6] do
    try
      addThm (Name.mkSimple s!"Controls.tauPartBad_{p}") (mkEqTrue (mkApp fE (mkRawNatLit p))) reflTrue
    catch _ => rejected := rejected + 1
  logInfo m!"network with a layer dropped ({layers.length - 1} of {layers.length}): {rejected} of 6 position checks rejected by the kernel"
