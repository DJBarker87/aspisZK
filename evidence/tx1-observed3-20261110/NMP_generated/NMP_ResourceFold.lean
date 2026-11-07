import NMP_CutAlgebra
import NLZ_Resources
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_ResourceFold
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code run Log)
open NLZ_Resources (Heap Frame)
/-- (bl)(3): stopped terminals have no post-abort resource state. -/
inductive Terminal (α : Type) where
 | returned (value : α) (heap : Heap)
 | failed (error : Error)
 | diverged
def result {α : Type} : Terminal α → Result α
 | .returned a _ => .ok a | .failed e => .fail e | .diverged => .div
def finalHeap {α : Type} : Terminal α → Option Heap
 | .returned _ h => some h | .failed _ => none | .diverged => none
/-- A parameterized resource fold, not a native producer. Its frame must be
proved at every returning child cut; arbitrary Occurrence records do not suffice. -/
inductive Chain {S α : Type} (step : S → Code (Sum α S)) (objectId : Nat) :
 Nat → S → Heap → Terminal α → Log → Prop where
 | returned {n s before after a log allowed}
   (head : run (step s) = (log,.ok (.inl a)))
   (frame : Frame allowed before after) (untouched : objectId ∉ allowed) :
   Chain step objectId (n+1) s before (.returned a after) log
 | next {n s t before middle out headLog suffix allowed}
   (head : run (step s) = (headLog,.ok (.inr t)))
   (frame : Frame allowed before middle) (untouched : objectId ∉ allowed)
   (tail : Chain step objectId n t middle out suffix) :
   Chain step objectId (n+1) s before out (headLog++suffix)
 | failed {n s before e log}
   (head : run (step s) = (log,.fail e)) :
   Chain step objectId (n+1) s before (.failed e) log
 | diverged {n s before log}
   (head : run (step s) = (log,.div)) :
   Chain step objectId (n+1) s before .diverged log
def fold {S α : Type} (step : S → Code (Sum α S)) : Nat → S → Code α
 | 0,_ => .step (.fail .panic) Code.done
 | n+1,s => PreparedHashCode.bind (step s) (fun p => match p with
   | .inl a => .done a | .inr t => fold step n t)
theorem value {S α : Type} {step : S → Code (Sum α S)} {objectId n s before out log}
 (chain : Chain step objectId n s before out log) :
 run (fold step n s) = (log,result out) := by
 induction chain with
 | returned head _ _ =>
  rw [fold,AuS1_Trace.run_bind,head]
  simp only [AuS1_Trace.continueRun,run,result,List.append_nil]
 | next head _ _ _ ih =>
  rw [fold,AuS1_Trace.run_bind,head]
  simp only [AuS1_Trace.continueRun,ih]
 | failed head => rw [fold,AuS1_Trace.run_bind,head];rfl
 | diverged head => rw [fold,AuS1_Trace.run_bind,head];rfl
/-- Returning paths preserve the objectId allocation by concrete child frames;
no corresponding assertion is demanded or invented for a stopped path. -/
theorem protected_return {S α : Type} {step : S → Code (Sum α S)} {objectId n s before out log}
 (chain : Chain step objectId n s before out log) :
 ∀ after, finalHeap out = some after → after.objects objectId = before.objects objectId := by
 induction chain with
 | returned _ frame untouched =>
  intro h same
  cases same
  exact frame.1 objectId untouched
 | next _ frame untouched _ ih =>
  intro h same
  exact (ih h same).trans (frame.1 objectId untouched)
 | failed _ => intro h same;cases same
 | diverged _ => intro h same;cases same
#print axioms value
#print axioms protected_return
end AspisR1.NMP_ResourceFold
end
