import NLT_NativeInvocation
set_option autoImplicit false
noncomputable section
namespace NLT_Continuation
open Aeneas Aeneas.Std Result NKE_Free
/-- Interpreter argument mismatch is retained explicitly, not excluded by
selecting only well-decoded native runs. -/
inductive Invalid {E A : Type} (Local : E → E → Prop) : Program E A → List E → Prop where
 | prim_ok {B : Type} (value : B) (next : B → Program E A) (events : List E)
   (tail : Invalid Local (next value) events) : Invalid Local (.prim (.ok value) next) events
 | call_ok {B : Type} (codec : Codec E B) (seed : Result B) (next : B → Program E A)
   (actual : E) (cut : Local (codec.encode seed) actual) (value : B)
   (decoded : codec.decode actual=some (.ok value)) (events : List E)
   (tail : Invalid Local (next value) events) : Invalid Local (.call codec seed next) (actual::events)
 | mismatch {B : Type} (codec : Codec E B) (seed : Result B) (next : B → Program E A)
   (actual : E) (cut : Local (codec.encode seed) actual) (decoded : codec.decode actual=none) :
   Invalid Local (.call codec seed next) [actual]
theorem no_invalid {E A : Type} (Local : E → E → Prop) (p : Program E A)
 (cuts : ∀ e∈(eval p).events,∀ actual,Local e actual → actual=e)
 (events : List E) (bad : Invalid Local p events) : False := by
 induction bad with
 | prim_ok value next events tail ih => exact ih cuts
 | call_ok codec seed next actual cut value decoded events tail ih =>
   have same:=cuts (codec.encode seed) (by cases seed <;> exact List.mem_cons_self) actual cut
   rw [same,codec.roundtrip] at decoded
   cases decoded
   exact ih (fun e member actual localCut=>cuts e (List.mem_cons_of_mem _ member) actual localCut)
 | mismatch codec seed next actual cut decoded =>
   have same:=cuts (codec.encode seed) (by cases seed <;> exact List.mem_cons_self) actual cut
   rw [same,codec.roundtrip] at decoded
   cases decoded
#print axioms no_invalid
end NLT_Continuation
namespace NLT_NativeInvocation
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved NKE_Free
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
inductive Invalid (H : Bytes → State) {X : Type} (d : aspis_core.digest.Digest32 X) (hash : X)
 {A : Type} : Program Event A → List (Occurrence H d hash) → Prop where
 | prim_ok {B : Type} (value : B) (next : B → Program Event A) (records : List (Occurrence H d hash))
   (tail : Invalid H d hash (next value) records) : Invalid H d hash (.prim (.ok value) next) records
 | call_ok {B : Type} (codec : Codec Event B) (seed : Result B) (next : B → Program Event A)
   (record : Occurrence H d hash)
   (same : NLT_NativeWindows.question record.entered=NLT_NativeWindows.question (codec.encode seed))
   (value : B) (decoded : codec.decode (actual record)=some (.ok value))
   (records : List (Occurrence H d hash)) (tail : Invalid H d hash (next value) records) :
   Invalid H d hash (.call codec seed next) (record::records)
 | mismatch {B : Type} (codec : Codec Event B) (seed : Result B) (next : B → Program Event A)
   (record : Occurrence H d hash)
   (same : NLT_NativeWindows.question record.entered=NLT_NativeWindows.question (codec.encode seed))
   (decoded : codec.decode (actual record)=none) : Invalid H d hash (.call codec seed next) [record]
end NLT_NativeInvocation
