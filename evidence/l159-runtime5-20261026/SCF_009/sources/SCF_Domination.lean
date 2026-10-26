import SCF_Recovery
import F3U_Averaging
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCF_Domination
open FS FS2
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open RawRecordedOracleExtractionMassBin OraclePortRefineJoin
attribute [local instance] Classical.propDecidable

/-- A generic consumer, NOT an instance of physical account transport. The
clean agreement premise must be derived on the actual shared experiment. -/
theorem pointwise_of_agreement (left right : RawCutProverCompiler.RunView)
    (bad : Prop)
    (clean : left.2.2 = true → ¬ bad →
      right.2.2 = true ∧ RecoveredInputAgreement left right) :
    failureMass left ≤ failureMass right + indicator bad := by
  by_cases collision : bad
  · have bounded : failureMass left ≤ 1 := by
      unfold failureMass
      apply le_trans (mean_mono ?_) (by rw [mean_const])
      intro coins
      by_cases failed : left.2.2 = true ∧ RawRecordedPublicSpendExtractorBin.extract left coins = none
      <;> simp [indicator, failed]
    have positive := F3T_Runtime.nonnegative right
    rw [indicator, if_pos collision]
    linarith
  · have transported : failureMass left ≤ failureMass right := by
      apply failureMass_le_of_recovered_inputs left right
      · intro accepted
        exact (clean accepted collision).1
      · intro accepted
        exact (clean accepted collision).2
    simpa only [indicator, if_neg collision, add_zero] using transported

#print axioms pointwise_of_agreement
end AspisR1.SCF_Domination
end
