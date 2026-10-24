import Port18COHERENCE_CheckedAccounting
open Lean in
run_elab do
  let all ← Port18COHERENCE_Load.load
  let selected ← Port18COHERENCE_Load.select all #[`AspisR1.Port17RELEASE_Invariant.tx1, `AspisR1.Port17RELEASE_Invariant.tx2, `AspisR1.Port17RELEASE_Domain.delegated, `AspisS1TopPrepareCode.installed_count, `AspisS1TopPrepareCode.installed_effects_count, `AspisR1.Port17RELEASE_Prepare.op7_count, `AspisR1.Port17RELEASE_Prepare.body_other, `AspisR1.Port17RELEASE_Prepare.budgets, `AspisR1.Port17RELEASE_Driver.weights, `AspisR1.Port17RELEASE_Driver.stages, `AspisR1.Port17RELEASE_Driver.rust, `AspisR1.Port17RELEASE_Effects.op7_effects_count, `AspisR1.Port17RELEASE_Accounting.budget, `AspisR1.Port17RELEASE_Accounting.log_length, `AspisR1.Port16CUT_Cuts.sourceOne_eq, `AspisR1.Port16CUT_Cuts.sourceTwo_eq, `AspisR1.Port16CUT_Driver.stages_eq, `AspisR1.Port1_Driver.rust, `AspisR1.Port1_Driver.stages, `AspisR1.Port6AUTH_Prefix.source, `AspisS1TopPrepareCode.body, `AspisS1TopPrepareCode.code, `AspisS1TopPrepareCode.sourceOps, `AspisS1TopPrepareSource.prepare]
  let env ← getEnv
  let mut count := 0
  for (n,c) in selected.toList do
    let some checked := env.checked.get.find? n | throwError "Missing reconstructed declaration {n}"
    unless Port18COHERENCE_Load.sameDeclaration c checked do
      throwError "Reconstructed expression/metadata differs: {n}"
    count := count + 1
    IO.println ("IDENTICAL " ++ n.toString)
  logInfo m!"Exact full declarations/types/proof and opaque values verified: {count}"
#print axioms AspisR1.Port17RELEASE_Invariant.tx1
#print axioms AspisR1.Port17RELEASE_Invariant.tx2
#print axioms AspisR1.Port17RELEASE_Domain.delegated
#print axioms AspisS1TopPrepareCode.installed_count
#print axioms AspisS1TopPrepareCode.installed_effects_count
#print axioms AspisR1.Port17RELEASE_Prepare.op7_count
#print axioms AspisR1.Port17RELEASE_Prepare.body_other
#print axioms AspisR1.Port17RELEASE_Prepare.budgets
#print axioms AspisR1.Port17RELEASE_Driver.weights
#print axioms AspisR1.Port17RELEASE_Driver.stages
#print axioms AspisR1.Port17RELEASE_Driver.rust
#print axioms AspisR1.Port17RELEASE_Effects.op7_effects_count
#print axioms AspisR1.Port17RELEASE_Accounting.budget
#print axioms AspisR1.Port17RELEASE_Accounting.log_length
#print axioms AspisR1.Port16CUT_Cuts.sourceOne_eq
#print axioms AspisR1.Port16CUT_Cuts.sourceTwo_eq
#print axioms AspisR1.Port16CUT_Driver.stages_eq
set_option pp.all true
#check @AspisR1.Port17RELEASE_Invariant.tx1
#check @AspisR1.Port17RELEASE_Invariant.tx2
#check @AspisR1.Port17RELEASE_Domain.delegated
#check @AspisS1TopPrepareCode.installed_count
#check @AspisS1TopPrepareCode.installed_effects_count
#check @AspisR1.Port17RELEASE_Prepare.op7_count
#check @AspisR1.Port17RELEASE_Prepare.body_other
#check @AspisR1.Port17RELEASE_Prepare.budgets
#check @AspisR1.Port17RELEASE_Driver.weights
#check @AspisR1.Port17RELEASE_Driver.stages
#check @AspisR1.Port17RELEASE_Driver.rust
#check @AspisR1.Port17RELEASE_Effects.op7_effects_count
#check @AspisR1.Port17RELEASE_Accounting.budget
#check @AspisR1.Port17RELEASE_Accounting.log_length
#check @AspisR1.Port16CUT_Cuts.sourceOne_eq
#check @AspisR1.Port16CUT_Cuts.sourceTwo_eq
#check @AspisR1.Port16CUT_Driver.stages_eq
set_option pp.all false
set_option pp.proofs false
#print AspisR1.Port17RELEASE_Domain.ReleaseCall
#print AspisR1.Port17RELEASE_Domain.CallsIn
#print AspisR1.Port17RELEASE_Domain.ReleaseBudgets
#print AspisR1.Port17RELEASE_Prepare.OtherBudgets
#print AspisR1.Port17RELEASE_Prepare.implementation
#print AspisR1.Port17RELEASE_Driver.remainingWeight
#print AspisR1.Port1_Driver.stages
#print AspisR1.Port1_Driver.rust
#print AspisR1.Port16CUT_Driver.next
#print AspisR1CurrentCaller.Ops
#print AspisR1PublicPreparation.RoundModel.Boundaries
#print AspisR1PublicPreparation.FinishModel.Boundaries
#print AdapterRw.Ops
#print AspisS1TopPrepareCode.sourceOps
#print AspisS1TopPrepareCode.body
