import FourColor.Reducibility.Cf110
import FourColor.Reducibility.Cf001
open Lean Elab Command
def kindOf : ConstantInfo → String
  | .defnInfo _ => "def" | .thmInfo _ => "thm" | _ => "other"
run_cmd do
  let env ← getEnv
  let mods : List Name := [`FourColor.Reducibility.Nets6, `FourColor.Reducibility.Nets14,
    `FourColor.Reducibility.Cf001, `FourColor.Reducibility.Cf110]
  for modName in mods do
    match env.getModuleIdx? modName with
    | none => logInfo m!"{modName}: not found"
    | some idx =>
      let cs := env.header.moduleData[idx.toNat]!.constants
      let defs := cs.filter (fun c => kindOf c == "def") |>.size
      let thms := cs.filter (fun c => kindOf c == "thm") |>.size
      let names := (cs.map fun c => s!"{c.name}[{kindOf c}]").toList
      logInfo m!"{modName}: {cs.size} constants ({defs} defs, {thms} thms, {cs.size - defs - thms} other): {names}"
