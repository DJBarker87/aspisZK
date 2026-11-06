import NLT_NativeWindows
set_option autoImplicit false
noncomputable section
namespace NLT_NativeInvocation
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved NKE_Free
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
abbrev Detail := NLT_Subcuts.Detail
/-- Every occurrence owns its interpreted input and nested cut. There is no
separate list of C04 histories to associate with an independent source log. -/
structure Occurrence (H : Bytes → State)
 {X : Type} (d : aspis_core.digest.Digest32 X) (hash : X) where
 entered : Event
 input : NLT_NativeWindows.Input entered
 detail : Detail H (NLT_NativeWindows.window H d hash entered input)
def actual {H : Bytes → State}
 {X : Type} {d : aspis_core.digest.Digest32 X} {hash : X} (o : Occurrence H d hash) : Event :=
 NLT_NativeWindows.window H d hash o.entered o.input
/-- Single caller continuation. In particular call_fail/call_div contain one
last cut and have no suffix constructor or independently selected endpoint. -/
inductive Invocation (H : Bytes → State)
 {X : Type} (d : aspis_core.digest.Digest32 X) (hash : X) {A : Type} :
 Program Event A → Result A → List (Occurrence H d hash) → Prop where
 | ret (value : A) : Invocation H d hash (.ret value) (.ok value) []
 | prim_ok {B : Type} (value : B) (next : B → Program Event A)
   (result : Result A) (records : List (Occurrence H d hash))
   (tail : Invocation H d hash (next value) result records) :
   Invocation H d hash (.prim (.ok value) next) result records
 | prim_fail {B : Type} (error : Error) (next : B → Program Event A) :
   Invocation H d hash (.prim (.fail error) next) (.fail error) []
 | prim_div {B : Type} (next : B → Program Event A) :
   Invocation H d hash (.prim .div next) .div []
 | call_ok {B : Type} (codec : Codec Event B) (seed : Result B) (next : B → Program Event A)
   (record : Occurrence H d hash) (same : NLT_NativeWindows.question record.entered=NLT_NativeWindows.question (codec.encode seed)) (value : B)
   (decoded : codec.decode (actual record)=some (.ok value)) (result : Result A)
   (records : List (Occurrence H d hash)) (tail : Invocation H d hash (next value) result records) :
   Invocation H d hash (.call codec seed next) result (record::records)
 | call_fail {B : Type} (codec : Codec Event B) (seed : Result B) (next : B → Program Event A)
   (record : Occurrence H d hash) (same : NLT_NativeWindows.question record.entered=NLT_NativeWindows.question (codec.encode seed)) (error : Error)
   (decoded : codec.decode (actual record)=some (.fail error)) :
   Invocation H d hash (.call codec seed next) (.fail error) [record]
 | call_div {B : Type} (codec : Codec Event B) (seed : Result B) (next : B → Program Event A)
   (record : Occurrence H d hash) (same : NLT_NativeWindows.question record.entered=NLT_NativeWindows.question (codec.encode seed))
   (decoded : codec.decode (actual record)=some .div) :
   Invocation H d hash (.call codec seed next) .div [record]
theorem erase {H : Bytes → State}
 {X : Type} {d : aspis_core.digest.Digest32 X} {hash : X} {A : Type}
 (p : Program Event A) (result : Result A) (records : List (Occurrence H d hash))
 (invocation : Invocation H d hash p result records) :
 NLT_Continuation.Invocation ((fun e actual=>∃ recorded (input : NLT_NativeWindows.Input recorded),
  NLT_NativeWindows.question recorded=NLT_NativeWindows.question e ∧
  actual=NLT_NativeWindows.window H d hash recorded input)) p result (records.map actual) := by
 induction invocation with
 | ret value => exact .ret value
 | prim_ok value next result records tail ih => exact .prim_ok value next result _ ih
 | prim_fail error next => exact .prim_fail error next
 | prim_div next => exact .prim_div next
 | call_ok codec seed next record same value decoded result records tail ih =>
   apply NLT_Continuation.Invocation.call_ok codec seed next (actual record) _ value decoded result _ ih
   exact ⟨record.entered,record.input,same,rfl⟩
 | call_fail codec seed next record same error decoded =>
   apply NLT_Continuation.Invocation.call_fail codec seed next (actual record) _ error decoded
   exact ⟨record.entered,record.input,same,rfl⟩
 | call_div codec seed next record same decoded =>
   apply NLT_Continuation.Invocation.call_div codec seed next (actual record) _ decoded
   exact ⟨record.entered,record.input,same,rfl⟩
set_option pp.proofs false
#print erase
#print axioms erase
end NLT_NativeInvocation
