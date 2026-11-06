import NLT_NativeFacts
import NLT_C04Installed
set_option autoImplicit false
noncomputable section
namespace NLT_C04NativeInstalled
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved NKE_Free
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep NLT_NativeInvocation
/-- Both returning and abort C04 packets are installed on subcuts projected
from the ONE parent continuation. No independent C04 log is hypothesized and
no allocator/ABI/observe/cuts argument remains outside the native relation. -/
theorem installed (H : Bytes → State) {X : Type} (d : aspis_core.digest.Digest32 X)
 (pub proof ck : Slice U8) (hash : X) (len : proof.val.length=57607)
 (root0 : NLP_InputDomain.Root0 ck proof) (result : R Unit) (records : List (Occurrence H d hash))
 (native : Invocation H d hash (NLT_NativeSource.skeleton H d pub proof ck hash) result records) :
 ∀ record∈records,NLT_C04Installed.Law H record.detail := by
 intro record atRecord
 let f:=NLT_FrameFromCuts.frame records
 exact NLT_C04Installed.at_event H f.resume f.pending (NLB_Parent.finish f.finish)
  d pub proof ck hash len root0 (actual record)
  (NLT_NativeFacts.member H d pub proof ck hash len result records native record atRecord) record.detail
set_option pp.proofs false
#print installed
#print axioms installed
end NLT_C04NativeInstalled
