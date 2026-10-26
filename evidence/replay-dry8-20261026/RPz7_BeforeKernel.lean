import Lean
import Rc10_Top
open Lean Elab Command
set_option pp.all true
set_option pp.universes true
set_option pp.fullNames true
set_option pp.explicit true
#print AspisR1.Rc10_Top.deployed
#print axioms AspisR1.Rc10_Top.deployed
run_cmd do
  let env ← getEnv
  let info := env.find? `AspisR1.Rc10_Top.deployed
  match info with
  | none => throwError "missing historical root"
  | some info => logInfo m!"RPZ7_KERNEL_TYPE {repr info.type}"
