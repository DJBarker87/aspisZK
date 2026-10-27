import GExp_ReadPrefix
import GExp_NativeBounds
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_Nonvacuity
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem partial_syscall (e : Error) (sha : Bytes → State) :
    S2W_ExtractionBoundary.RuntimeSyscall (fun _ => .fail e) sha := by
  constructor
  intro parts digest impossible
  cases impossible

theorem failed_attempt (e : Error) (parts : SdkC_Source.Parts) :
    SdkC_Source.run (fun _ => .fail e) (SdkC_Source.digestCode parts) [] =
      (.fail e,[⟨parts,.fail e⟩]) := SdkC_Source.failed_digest _ parts e rfl

/-- The new whole-first syntax contains literal all-input early rejection;
no all-input acceptance or total syscall condition is smuggled into it. -/
theorem first_rejects (base : AspisR1CurrentCaller.Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Unit)
    (semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) :
    SdkC_Source.run hashv (GExp_FirstCode.code base B std hashv D semantic pub proof 0#usize) [] =
      (ok (.Err AspisR1CurrentCaller.verifier.Error.Parse),[]) := by
  rfl

#print axioms partial_syscall
#print axioms failed_attempt
#print axioms first_rejects
end AspisR1.GExp_Nonvacuity
end
