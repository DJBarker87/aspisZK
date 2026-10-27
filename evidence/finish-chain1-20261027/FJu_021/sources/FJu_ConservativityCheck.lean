import FJu_Conservativity
import Lean
open Lean Meta Elab
run_meta do
  let before ← getConstInfo ``AspisR1.FJp_Top.deployed
  let after ← getConstInfo ``AspisR1.FJu_Conservativity.deployed
  unless before.levelParams.length == after.levelParams.length do
    throwError "Universe binder count changed"
  let levels := before.levelParams.map Level.param
  unless before.type.instantiateLevelParams before.levelParams levels ==
      after.type.instantiateLevelParams after.levelParams levels do
    throwError "Conservativity type differs from original FJp root"
  logInfo "CONSERVATIVITY: exact original FJp root kernel type, all hypotheses and conclusions"
#print axioms AspisR1.FJu_Conservativity.deployed
