import Statements
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  for n in [``RiemannHypothesis, ``riemannZeta, ``DirichletCharacter.LFunction, ``DirichletCharacter, ``DirichletCharacter.IsPrimitive] do
    IO.println s!"{n} from module {env.header.moduleNames[(env.getModuleIdxFor? n).get!.toNat]!}"
#print RiemannHypothesis
#print RiemannZetaZerosOnLine
#print DirichletLNonvanishingRightOfHalf
#print DirichletLZerosOnLine
#print PrimitiveDirichletLZerosOnLine
example : RiemannZetaZerosOnLine = RiemannHypothesis := rfl
#print axioms RiemannZetaZerosOnLine
