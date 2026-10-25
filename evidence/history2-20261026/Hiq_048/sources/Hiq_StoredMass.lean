import OraclePortRuntimeBindingC7
import Hiq_MeanSum
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_StoredMass
open FS FS2 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.CausalFirstHitUnionBound AspisV8R19.OracleResampling
open OraclePortStoredExperimentC4 OraclePortRuntimeBindingC7 OraclePortStoredAdmissionC4
open RawRecordedOracleExtractionMassBin

theorem failure_le_one (run : RawCutProverCompiler.RunView) : failureMass run ≤ 1 := by
  unfold failureMass
  have bound := mean_mono (fun coins : GSConcreteByteDecoderBank.RawCoins =>
    indicator_le_one (run.2.2 = true ∧ RawRecordedPublicSpendExtractorBin.extract run coins = none))
  simpa only [mean_const] using bound

theorem runtime_le_one (v : View Bytes State (Option RunView)) : runtimeMass v ≤ 1 := by
  cases h : v.2 with
  | none => simp only [runtimeMass,h]; norm_num
  | some run => exact failure_le_one (view run)

theorem rejected_zero (run : RunView) (rejected : run.2.2 ≠ true) : failureMass (view run) = 0 := by
  unfold failureMass
  simp only [view] at *
  simp [rejected,indicator,mean_const]

#print axioms failure_le_one
#print axioms runtime_le_one
#print axioms rejected_zero
end AspisR1.Hiq_StoredMass
end
