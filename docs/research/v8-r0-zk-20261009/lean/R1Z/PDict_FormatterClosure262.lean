import R1Z.PDict_ArrayReference244
import R1Z.ProverRwP6BodyData
import R1Z.PrivacyR1HeadlineDeployedReal
import R1Z.PV_CB3_Afterstate
import R1Z.PV_CB3_Op225Source
import R1Z.PV_CB3_Op229Source
import R1Z.PV_CB3_Op246Source
import R1Z.PV_CB3_PoleRows
import Lean
open Lean Elab Command
#print axioms Aeneas.Std.core.fmt.Formatter
#print axioms ProverRwFull.ExternalFuns
#print axioms R1Z.ProverRwP6BodyData.refinement_of_data
#print axioms ProverRwFull.ExternalTypes.op0
#print axioms ProverRwFull.ExternalTypes.op1
#print axioms ProverRwFull.ExternalTypes.op2
#print axioms ProverRwFull.ExternalTypes.op3
#print axioms ProverRwFull.ExternalTypes.op4
#print axioms ProverRwFull.ExternalTypes.op5
#print axioms ProverRwFull.ExternalTypes.op6
#print axioms ProverRwFull.ExternalTypes.op7
#print axioms ProverRwFull.ExternalTypes.op8
#print axioms ProverRwFull.ExternalTypes.op9
#print axioms ProverRwFull.ExternalTypes.op10
#print axioms ProverRwFull.ExternalTypes.op11
#print axioms ProverRwFull.ExternalTypes.op12
#print axioms ProverRwFull.ExternalTypes.op13
#print axioms ProverRwFull.ExternalTypes.op14
#print axioms ProverRwFull.ExternalTypes.op15
#print axioms ProverRwFull.ExternalTypes.op16
#print axioms ProverRwFull.ExternalTypes.op17
#print axioms ProverRwFull.ExternalTypes.op18
#print axioms ProverRwFull.ExternalTypes.op19
#print axioms ProverRwFull.ExternalTypes.op20
#print axioms ProverRwFull.ExternalTypes.op21
#print axioms ProverRwFull.ExternalTypes.op22
#print axioms ProverRwFull.ExternalTypes.op23
#print axioms ProverRwFull.ExternalTypes.op24
#print axioms ProverRwFull.ExternalTypes.op25
#print axioms ProverRwFull.ExternalTypes.op26
#print axioms ProverRwFull.ExternalTypes.op27

run_cmd do
  let env ← getEnv
  for (n, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let owner := env.header.moduleNames[idx]!
      let text := owner.toString
      if text.startsWith "R1Z.PDict_" || text.startsWith "R1Z.ProverRw" ||
          text.startsWith "R1Z.PV_CB_" || text.startsWith "R1Z.PV_CB3_" then
        logInfo m!"OWNER|{owner}|{n}"
        elabCommand (← `(command| #print axioms $(mkIdent n)))
