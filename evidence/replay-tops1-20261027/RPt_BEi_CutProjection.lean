import RPt_BEi_ExecutionHistory
import RPt_BEh_Scope
import RPz8_RPx_AttemptPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEi_CutProjection
open Aeneas Aeneas.Std Result SdkC_Source BEi_Execution

/-- Operational digest steps imply the computed source log; no state frame or
syscall totality is needed. The execution relation must be instantiated. -/
theorem source {S A : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest)
    (binding : ∀ parts state, (call parts state).1 = hashv parts)
    (code : Code A) (state after : S) (before log : Log) (value : Result A)
    (execution : Executes call code state before value after log) :
    (value,log) = SdkC_Source.run hashv code before := by
  have same := BEf_Carrier.source call hashv binding code state before
  rw [BEi_Execution.sound call code state after before log value execution] at same
  exact same

/-- Native-local acceptance and rejection correspondence follows once the
actual operational cut is associated. This does not construct that cut. -/
theorem observation {S A E : Type} (call : Parts → S → Result Digest × S)
    (code : Code (core.result.Result A E)) (state after : S) (before log : Log)
    (value : Result (core.result.Result A E))
    (execution : Executes call code state before value after log) :
    BEh_Scope.Law (value,after,log) (BEf_Carrier.run call code state before) := by
  rw [BEi_Execution.sound call code state after before log value execution]
  exact BEh_Scope.reflexive _

/-- Complete attempted-address prefix, including a final failed syscall. -/
theorem attempted {S A : Type} (call : Parts → S → Result Digest × S)
    (hashv : Parts → Result Digest)
    (binding : ∀ parts state, (call parts state).1 = hashv parts)
    (sha256 H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
    (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (code : Code A) (state after : S) (before log : Log) (value : Result A)
    (execution : Executes call code state before value after log) :
    ∃ kept remaining,
      RPx_AttemptPrefix.addresses log = RPx_AttemptPrefix.addresses before ++ kept ∧
      (AspisV8R19.MemoizedProgramLaw.eval H (SdkC_Oracle.program code)).1.map Prod.fst = kept ++ remaining := by
  have same := congrArg Prod.snd (source call hashv binding code state after before log value execution)
  change log = (SdkC_Source.run hashv code before).2 at same
  rw [same]
  exact RPx_AttemptPrefix.transport code hashv sha256 H p1 syscall before

#print axioms source
#print axioms observation
#print axioms attempted
end AspisR1.BEi_CutProjection
end
