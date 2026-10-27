import RPx_AttemptPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.RPx_FailedQuery
open Aeneas Aeneas.Std Result CheckpointBytes5Effect
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw

/-- Non-vacuity for the failed-syscall branch: successful readLog is empty,
but the attempted address is charged once and present in the ideal prefix. -/
theorem counted {A : Type} (parts : SdkC_Source.Parts) (k : SdkC_Source.Digest → Code A)
    (error : Error) (H : Bytes → State) :
    (SdkC_Source.run (fun _=>.fail error) (.read parts k) []).2.length=1 ∧
    SdkC_Source.readLog (SdkC_Source.run (fun _=>.fail error) (.read parts k) []).2=[] ∧
    RPx_AttemptPrefix.addresses (SdkC_Source.run (fun _=>.fail error) (.read parts k) []).2=[flatten parts] ∧
    ∃ rest : List Bytes,(eval H (SdkC_Oracle.program (.read parts k))).1.map Prod.fst=flatten parts::rest := by
  refine ⟨rfl,rfl,rfl,(eval H (SdkC_Oracle.program (k (encodeState (H (flatten parts)))))).1.map Prod.fst,?_⟩
  simp only [SdkC_Oracle.program,eval,List.map_cons]

#print axioms counted
end AspisR1.RPx_FailedQuery
end
