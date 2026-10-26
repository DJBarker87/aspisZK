import SCE_Experiment
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_FailureZero
open AspisV8R19.OracleResampling AspisV8R19.UniformStateFirstHit
open AspisV8R19.CausalFirstHitUnionBound
open RawRecordedOracleExtractionMassBin
attribute [local instance] Classical.propDecidable

theorem rejected (run : RawCutProverCompiler.RunView) (accept : run.2.2 ≠ true) :
    failureMass run = 0 := by
  unfold failureMass
  simp [accept,indicator,mean_const]

#print axioms rejected
end AspisR1.SCE_FailureZero
end
