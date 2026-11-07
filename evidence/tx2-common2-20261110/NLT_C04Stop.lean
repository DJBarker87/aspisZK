import NLT_NativeSource
set_option autoImplicit false
noncomputable section
namespace NLT_C04Stop
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved NKE_Free
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep NLT_NativeInvocation
/-- Actual native nonreturning C04 subcut. There is deliberately NO returned
reply and NO equation to the total-H returning reference. -/
structure Cut (H : Bytes → State) where
 proof : Slice U8
 prepared : verifier.Prepared
 folded : Array U8 32#usize
 inside : NLL.History
 pending : NLL.Pending
 child : NLL_BatchAbort.Invocation H proof prepared folded 1#usize inside pending
/-- A question marker only, never a claimed returned native divergence. -/
def question {H : Bytes → State} (cut : Cut H) : Event :=
 .merkle cut.proof cut.prepared cut.folded .div
/-- SAME continuation and actual replies before C04. The stopped constructor
has no continuation premise or suffix. The child may abort even when its
returning reference would return Ok. -/
inductive At (H : Bytes → State) {X : Type} (d : aspis_core.digest.Digest32 X) (hash : X)
 {A : Type} : Program Event A → List (Occurrence H d hash) → Cut H → Prop where
 | prim_ok {B : Type} (value : B) (next : B → Program Event A)
   (records : List (Occurrence H d hash)) (cut : Cut H)
   (tail : At H d hash (next value) records cut) : At H d hash (.prim (.ok value) next) records cut
 | call_ok {B : Type} (codec : Codec Event B) (seed : Result B) (next : B → Program Event A)
   (record : Occurrence H d hash)
   (same : NLT_NativeWindows.question record.entered=NLT_NativeWindows.question (codec.encode seed))
   (value : B) (decoded : codec.decode (actual record)=some (.ok value))
   (records : List (Occurrence H d hash)) (cut : Cut H)
   (tail : At H d hash (next value) records cut) : At H d hash (.call codec seed next) (record::records) cut
 | stopped {B : Type} (codec : Codec Event B) (seed : Result B) (next : B → Program Event A)
   (cut : Cut H) (same : NLT_NativeWindows.question (codec.encode seed)=question cut) :
   At H d hash (.call codec seed next) [] cut
set_option pp.proofs false
#print Cut
#print At
end NLT_C04Stop
