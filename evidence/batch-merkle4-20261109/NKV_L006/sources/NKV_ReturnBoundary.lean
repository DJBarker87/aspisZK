import NKV_LoopTransport
set_option autoImplicit false
noncomputable section
namespace NKV_ReturnBoundary
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open NKV_StepErasure NKV_LoopTransport

def returned (x : Out) : Result (Reply × Indices × Values) :=
 ok (x.2.2.1,x.1,x.2.1)

def cohort (x : Out) : Result (Reply × Indices × Values) :=
 match eraseOut x with
 | (i,v,none) => fail .panic
 | (i,v,some r) => ok (r,i,v)

/-- Consumer rejection observation retains every successful mutable value.
It does not modify the adopted cohort or claim all its errors are Result.fail. -/
def reject : Result (Reply × Indices × Values) → Result (Unit × Indices × Values)
 | .ok (.Ok u,i,v) => ok (u,i,v)
 | .ok (.Err _,_,_) => fail .panic
 | .fail e => fail e
 | .div => div

def WellClassified (x : Out) : Prop := x.2.2.2=true → x.2.2.1≠.Ok ()

theorem preserved (i : Indices) (v : Values) (r : Reply) :
 cohort (i,v,r,false)=returned (i,v,r,false) := rfl

theorem lost (i : Indices) (v : Values) (r : Reply) :
 cohort (i,v,r,true)=fail .panic := rfl

/-- The duplicate Err arm is preserved by the actual pending-return boundary.
Thus a literal all-errors iff Result.fail statement is false at this boundary. -/
theorem duplicate_preserved (i : Indices) (v : Values) :
 cohort (i,v,.Err .Merkle,false)=ok (.Err .Merkle,i,v) ∧
 cohort (i,v,.Err .Merkle,false)≠fail .panic := by
 exact ⟨rfl,by intro h;cases h⟩

theorem observed (x : Out) (well : WellClassified x) :
 reject (cohort x)=reject (returned x) := by
 rcases x with ⟨i,v,r,b⟩
 cases b with
 | false => rfl
 | true =>
   cases r with
   | Err e => rfl
   | Ok u => cases u;exact (well rfl rfl).elim

/-- Identical ordered-effects and oracle-query prefix; terminal observation
adds no event. Event can be a sum carrying both event classes. -/
def observeTrace {Event : Type} (prefix : List Event)
 (out : Result (Reply × Indices × Values)) := (prefix,reject out)

theorem prefix_transport {Event : Type} (prefix : List Event) (x : Out)
 (well : WellClassified x) :
 observeTrace prefix (cohort x)=observeTrace prefix (returned x) := by
 unfold observeTrace
 rw [observed x well]

set_option pp.proofs false
#print observed
#print prefix_transport
#print axioms preserved
#print axioms lost
#print axioms duplicate_preserved
#print axioms observed
#print axioms prefix_transport
end NKV_ReturnBoundary
end
