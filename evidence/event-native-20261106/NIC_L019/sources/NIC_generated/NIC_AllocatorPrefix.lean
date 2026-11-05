import NIC_AbortPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIC_AllocatorPrefix
open Aeneas Aeneas.Std Result CheckpointBytes5Effect

/-- The same nonreturning allocation boundary also admits an abstract fail
terminal. This is an Aeneas partial outcome, never a Rust Box Err variant. -/
theorem fail {A B C : Type}
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (error : Error) (suffix : B → Code A) (context : C) (prior : SdkC_Source.Log) :
 (context,SdkC_Source.run hashv (.step (.fail error : Result B) suffix) prior)=
 (context,(.fail error,prior)) := by
 have t : NGQ_Cuts.Trace hashv (.step (.fail error : Result B) suffix) (.fail error) [] :=
   .stepFail _ _ error rfl
 simpa only [List.append_nil] using congrArg (fun r => (context,r)) (NGQ_Cuts.run t prior)

/-- Both partial terminals have the same prior-log frame, universally over the
continuation and typed allocation payload. The allocator/runtime realization
row chooses the physical terminal; no totality is asserted. -/
theorem stopped {A B C : Type}
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (stop : NIA_ScalarFailures.Stop) (suffix : B → Code A)
 (context : C) (prior : SdkC_Source.Log) :
 (context,SdkC_Source.run hashv (.step (stop.result : Result B) suffix) prior)=
 (context,(stop.result,prior)) := by
 cases stop with
 | fail error => exact fail hashv error suffix context prior
 | div => exact NIC_AbortPrefix.allocation_div hashv suffix context prior

#print axioms fail
#print axioms stopped
end AspisR1.NIC_AllocatorPrefix
