import NLT_Interpreted
import NLT_Continuation
set_option autoImplicit false
noncomputable section
namespace NLT_Subcuts
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved NKE_Free
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Returning and abort C04 subcuts belong to the actual entered parent event.
A returning Result is derived later from the CLOSED child packet; it is NOT
a field of this type. Abort can decorate only a nonreturning parent event. -/
inductive Detail (H : Bytes → State) : Event → Type where
 | ordinary (e : Event) (notMerkle : ∀ pr p folded reply,e≠Event.merkle pr p folded reply) : Detail H e
 | returning (pr : Slice U8) (p : verifier.Prepared) (folded : Array U8 32#usize) (reply : R Unit)
   (inside : NLL.History) (out : NLL.Reply)
   (child : NLL_BatchSource.Invocation H pr p folded 1#usize inside out) :
   Detail H (.merkle pr p folded reply)
 | aborting (pr : Slice U8) (p : verifier.Prepared) (folded : Array U8 32#usize) (error : Error)
   (inside : NLL.History) (pending : NLL.Pending)
   (child : NLL_BatchAbort.Invocation H pr p folded 1#usize inside pending) :
   Detail H (.merkle pr p folded (.fail error))
/-- Every occurrence owns its interpreted input and nested cut. There is no
separate list of C04 histories to associate with an independent source log. -/
structure Occurrence (f : NLT_Interpreted.Uninstalled) (H : Bytes → State)
 {X : Type} (d : aspis_core.digest.Digest32 X) (hash : X) where
 entered : Event
 input : NLT_Interpreted.Input entered
 detail : Detail H (NLT_Interpreted.window f H d hash entered input)
def actual {f : NLT_Interpreted.Uninstalled} {H : Bytes → State}
 {X : Type} {d : aspis_core.digest.Digest32 X} {hash : X} (o : Occurrence f H d hash) : Event :=
 NLT_Interpreted.window f H d hash o.entered o.input
/-- Single caller continuation. In particular call_fail/call_div contain one
last cut and have no suffix constructor or independently selected endpoint. -/
inductive Invocation (f : NLT_Interpreted.Uninstalled) (H : Bytes → State)
 {X : Type} (d : aspis_core.digest.Digest32 X) (hash : X) {A : Type} :
 Program Event A → Result A → List (Occurrence f H d hash) → Prop where
 | ret (value : A) : Invocation f H d hash (.ret value) (.ok value) []
 | prim_ok {B : Type} (value : B) (next : B → Program Event A)
   (result : Result A) (records : List (Occurrence f H d hash))
   (tail : Invocation f H d hash (next value) result records) :
   Invocation f H d hash (.prim (.ok value) next) result records
 | prim_fail {B : Type} (error : Error) (next : B → Program Event A) :
   Invocation f H d hash (.prim (.fail error) next) (.fail error) []
 | prim_div {B : Type} (next : B → Program Event A) :
   Invocation f H d hash (.prim .div next) .div []
 | call_ok {B : Type} (codec : Codec Event B) (seed : Result B) (next : B → Program Event A)
   (record : Occurrence f H d hash) (same : record.entered=codec.encode seed) (value : B)
   (decoded : codec.decode (actual record)=some (.ok value)) (result : Result A)
   (records : List (Occurrence f H d hash)) (tail : Invocation f H d hash (next value) result records) :
   Invocation f H d hash (.call codec seed next) result (record::records)
 | call_fail {B : Type} (codec : Codec Event B) (seed : Result B) (next : B → Program Event A)
   (record : Occurrence f H d hash) (same : record.entered=codec.encode seed) (error : Error)
   (decoded : codec.decode (actual record)=some (.fail error)) :
   Invocation f H d hash (.call codec seed next) (.fail error) [record]
 | call_div {B : Type} (codec : Codec Event B) (seed : Result B) (next : B → Program Event A)
   (record : Occurrence f H d hash) (same : record.entered=codec.encode seed)
   (decoded : codec.decode (actual record)=some .div) :
   Invocation f H d hash (.call codec seed next) .div [record]
theorem erase {f : NLT_Interpreted.Uninstalled} {H : Bytes → State}
 {X : Type} {d : aspis_core.digest.Digest32 X} {hash : X} {A : Type}
 (p : Program Event A) (result : Result A) (records : List (Occurrence f H d hash))
 (invocation : Invocation f H d hash p result records) :
 NLT_Continuation.Invocation (NLT_Interpreted.Local f H d hash) p result (records.map actual) := by
 induction invocation with
 | ret value => exact .ret value
 | prim_ok value next result records tail ih => exact .prim_ok value next result _ ih
 | prim_fail error next => exact .prim_fail error next
 | prim_div next => exact .prim_div next
 | call_ok codec seed next record same value decoded result records tail ih =>
   apply NLT_Continuation.Invocation.call_ok codec seed next (actual record) _ value decoded result _ ih
   rw [←same]
   exact ⟨record.input,rfl⟩
 | call_fail codec seed next record same error decoded =>
   apply NLT_Continuation.Invocation.call_fail codec seed next (actual record) _ error decoded
   rw [←same]
   exact ⟨record.input,rfl⟩
 | call_div codec seed next record same decoded =>
   apply NLT_Continuation.Invocation.call_div codec seed next (actual record) _ decoded
   rw [←same]
   exact ⟨record.input,rfl⟩
set_option pp.proofs false
#print erase
#print axioms erase
end NLT_Subcuts
