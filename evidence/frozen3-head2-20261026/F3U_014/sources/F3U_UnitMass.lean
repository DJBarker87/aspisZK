import F3T_Runtime
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_UnitMass
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound
open RawRecordedOracleExtractionMassBin
attribute [local instance] Classical.propDecidable

theorem failure_le_one (run : RawCutProverCompiler.RunView) : failureMass run≤1 := by
  unfold failureMass
  apply le_trans (mean_mono ?_) (by rw [mean_const])
  intro coins
  by_cases h : run.2.2=true ∧ RawRecordedPublicSpendExtractorBin.extract run coins=none <;> simp [indicator,h]

theorem rejected (run : RawCutProverCompiler.RunView) (rejected : run.2.2≠true) : failureMass run=0 := by
  unfold failureMass
  simp [rejected,indicator,mean_const]

theorem runtime_le_one (run : Option F3T_Experiment.RunView) (log : List (Bytes × State)) :
    F3T_Runtime.runtimeMass (log,run)≤1 := by
  cases run with
  | none => exact zero_le_one
  | some run => exact failure_le_one _

#print axioms failure_le_one
#print axioms rejected
#print axioms runtime_le_one
end AspisR1.F3U_UnitMass
end
