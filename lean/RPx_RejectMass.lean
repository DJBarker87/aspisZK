import F3T_Runtime
set_option autoImplicit false
noncomputable section
namespace AspisR1.RPx_RejectMass
open FS FS2 AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_Experiment F3T_Runtime RawRecordedOracleExtractionMassBin

theorem rejected (run : RunView) (reject : run.2.2=false) : failureMass (view run)=0 := by
  unfold failureMass
  simp only [view,reject,Bool.false_eq_true,indicator,false_and,if_false,mean_const]

theorem runtime (r : Runtime) (H : Bytes → State)
    (reject : ∀ run,(eval H r).2=some run → run.2.2=false) : runtimeMass (eval H r)=0 := by
  unfold runtimeMass
  cases observed : (eval H r).2 with
  | none => rfl
  | some run => exact rejected run (reject run observed)

#print axioms rejected
#print axioms runtime
end AspisR1.RPx_RejectMass
end
