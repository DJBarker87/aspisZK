import NNH_064SourceDetails
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_064ProgramRecords
open Aeneas Aeneas.Std NJU_CommonObserved NKE_Free NLT_NativeInvocation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Structural native execution of a source program with computed per-call
records. The local record equality is discharged by SourceInputs.actual at
all reached calls; this helper is never exported as a final hypothesis. -/
theorem execute {A X : Type} (H : Bytes → State) (d : VTop_Stages.aspis_core.digest.Digest32 X)
 (hash : X) (p : Program Event A)
 (record : (e : Event) → e∈(eval p).events → Occurrence H d hash)
 (same : ∀ e h, actual (record e h)=e)
 (question : ∀ e h, NLT_NativeWindows.question (record e h).entered=NLT_NativeWindows.question e) :
 Invocation H d hash p (eval p).result
  ((eval p).events.pmap (fun e h=>record e h) (fun _ h=>h)) := by
 induction p with
 | ret value => exact .ret value
 | prim reply next ih =>
   cases reply with
   | fail error => exact .prim_fail error next
   | div => exact .prim_div next
   | ok value => exact .prim_ok value next _ _ (ih value record same question)
 | call codec seed next ih =>
   cases seed with
   | fail error =>
     let h : codec.encode (.fail error)∈(eval (.call codec (.fail error) next)).events := List.mem_singleton_self _
     apply Invocation.call_fail codec (.fail error) next (record _ h) (question _ h) error
     rw [same _ h]
     exact codec.roundtrip _
   | div =>
     let h : codec.encode .div∈(eval (.call codec .div next)).events := List.mem_singleton_self _
     apply Invocation.call_div codec .div next (record _ h) (question _ h)
     rw [same _ h]
     exact codec.roundtrip _
   | ok value =>
     let h : codec.encode (.ok value)∈(eval (.call codec (.ok value) next)).events := List.mem_cons_self
     refine Invocation.call_ok codec (.ok value) next (record _ h) (question _ h) value ?_ _ _ ?_
     · rw [same _ h]; exact codec.roundtrip _
     · change Invocation H d hash (next value) (eval (next value)).result _
       convert ih value (fun e mem=>record e (List.mem_cons_of_mem _ mem))
        (fun e mem=>same e (List.mem_cons_of_mem _ mem))
        (fun e mem=>question e (List.mem_cons_of_mem _ mem)) using 1
       apply List.pmap_congr_left
       intro e mem h1 h2
       rfl
#print axioms execute
end AspisR1.NNH_064ProgramRecords
