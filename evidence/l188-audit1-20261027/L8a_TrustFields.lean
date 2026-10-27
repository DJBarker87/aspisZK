import Lean
import RPz8_Rc10_Top
import RPz8_ARX_Root
open Lean Elab Command
#print AspisR1.S2W_ExtractionBoundary.P1
#print axioms AspisR1.S2W_ExtractionBoundary.P1
#print AspisR1.S2W_ExtractionBoundary.AeneasExtraction
#print axioms AspisR1.S2W_ExtractionBoundary.AeneasExtraction
#print AspisR1.S2W_ExtractionBoundary.RuntimeSyscall
#print axioms AspisR1.S2W_ExtractionBoundary.RuntimeSyscall
#print AspisR1.AdapterRw.RuntimeEntrypointAdmission
#print axioms AspisR1.AdapterRw.RuntimeEntrypointAdmission
#print AspisR1.S2Trust.S2TrustedSdkBorrow
#print axioms AspisR1.S2Trust.S2TrustedSdkBorrow
#print AspisR1.S2W_D189Consolidation.RuntimeEntrypointAdmission
#print axioms AspisR1.S2W_D189Consolidation.RuntimeEntrypointAdmission
#print AspisR1.S2W_DigestExtraction.AeneasExtraction
#print axioms AspisR1.S2W_DigestExtraction.AeneasExtraction
#print AspisR1.S2X.CheckpointVersionBinding
#print axioms AspisR1.S2X.CheckpointVersionBinding
#print AspisR1.S2W_D189Wrappers.Allocator
#print axioms AspisR1.S2W_D189Wrappers.Allocator
#print AspisR1.Port1_Library.TrustedStd
#print axioms AspisR1.Port1_Library.TrustedStd
#print AspisR1.S2W_TrustedStd.TrustedStd
#print axioms AspisR1.S2W_TrustedStd.TrustedStd
#print AspisR1.S2W_AuthenticatedInputs.CheckpointVersionBinding
#print axioms AspisR1.S2W_AuthenticatedInputs.CheckpointVersionBinding
#print AspisR1.CPR_DataPersistence.TwoTransactionLaw
#print axioms AspisR1.CPR_DataPersistence.TwoTransactionLaw
#print AspisR1.CPR_DataPersistence.visible
#print axioms AspisR1.CPR_DataPersistence.visible
#print AspisR1.CPR_Persistence.TwoTransactionLaw
#print axioms AspisR1.CPR_Persistence.TwoTransactionLaw
#print AspisR1.CPH_Game.DeployedPairExecution
#print axioms AspisR1.CPH_Game.DeployedPairExecution
run_cmd do
  let env := (← getEnv).setExporting false
  for root in #[`AspisR1.Rc10_Top.deployed, `AspisR1.ARX_Root.deployed] do
    let some c := env.checked.get.find? root | throwError "missing root {root}"
    logInfo m!"L8A_KERNEL_STATEMENT {(Json.mkObj [("name", toJson c.name.toString), ("levelParamsRepr", toJson (repr c.levelParams).pretty), ("typeRepr", toJson (repr c.type).pretty)]).compress}"
