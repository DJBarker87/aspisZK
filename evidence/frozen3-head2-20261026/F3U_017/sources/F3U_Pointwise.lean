import F3U_UnitMass
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_Pointwise
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound
open RawRecordedOracleExtractionMassBin
attribute [local instance] Classical.propDecidable

theorem failure_charge (source model : RawCutProverCompiler.RunView) (collision : Prop)
    (joined : source.2.2=true → source=model ∨ collision) :
    failureMass source≤failureMass model+indicator collision := by
  by_cases accepted : source.2.2=true
  · rcases joined accepted with same | bad
    · rw [same]
      exact le_add_of_nonneg_right (by unfold indicator;split <;> norm_num)
    · rw [indicator,if_pos bad]
      exact (F3U_UnitMass.failure_le_one source).trans
        (le_add_of_nonneg_left (F3T_Runtime.nonnegative model))
  · rw [F3U_UnitMass.rejected source accepted]
    exact add_nonneg (F3T_Runtime.nonnegative model) (by unfold indicator;split <;> norm_num)

#print axioms failure_charge
end AspisR1.F3U_Pointwise
end
