import FJv_Deployed
import FJv_Specialised
import FJv_Nonvacuity
import FJu_Top
import Lean
set_option pp.all true
set_option pp.deepTerms true
set_option pp.fullNames true
set_option pp.universes true
open Lean Meta Elab
run_meta do
  for n in [``AspisR1.FJu_Top.deployed,``AspisR1.FJv_Top.deployed,
      ``AspisR1.FJv_Specialised.deployed,``AspisR1.FJv_Deployed.deployed] do
    let i ← getConstInfo n
    logInfo m!"BEGIN KERNEL TYPE {n}\n{← ppExpr i.type}\nEND KERNEL TYPE {n}"
#print AspisR1.FJu_GlobalOwners.Owners
#print AspisR1.FJu_Remaining.Holds
#print AspisR1.FJu_Remaining.Endpoint
#print AspisR1.FJv_GlobalOwners.Owners
#print AspisR1.FJu_Finish.Outcome
#print AspisR1.FJv_Finish.Outcome
#print AspisR1.FJv_DFinish.Outcome
#print AspisR1.IDa_Deployed.Uninstalled
#print AspisR1.IDa_Deployed.deployedConfiguration
#print axioms AspisR1.FJv_Top.deployed
#print axioms AspisR1.FJv_Deployed.deployed
#print axioms AspisR1.FJv_Specialised.deployed
#print axioms AspisR1.FJv_Nonvacuity.conditional
#print axioms AspisR1.FJv_Nonvacuity.equivalent
#print axioms AspisR1.FJv_Nonvacuity.specialised
