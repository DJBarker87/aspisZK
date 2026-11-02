import R1Z.PV_V263_MapSpine
import R1Z.PV_V263_OutputShape
/-! The explicit inner source loop, including every item push. This corrects
an omission in the candidate MapSpine. VecCall is still a method boundary;
std allocation/store/drop lowering is not supplied by this module. -/
set_option autoImplicit false
namespace R1Z.PV_V263_SourceItems
open Aeneas Aeneas.Std PV_V263_World PV_V263_MapSpine

/-- Source order: evaluate f(i), push the result, then increment completed.
The list cons implements the logical pushed value; the vector method retains
its own state, events and every possible failure before the next callback. -/
def step {S A : Type} (runtime : Runtime S) (layouts : Layouts)
    (n k : Nat) (callback : Nat → Q S A) (i : Nat) : Q S A :=
  PV_V263_World.bind (callback i) fun value =>
    PV_V263_World.bind
      (runtime.vector (.push 0 k (i-PV_RunJoin_WorkRange35.start n k) layouts.item)) fun _ =>
      PV_V263_World.lift (.ok value)

def run {S A : Type} (runtime : Runtime S) (layouts : Layouts)
    (n k : Nat) (callback : Nat → Q S A) : Q S (List A) :=
  PV_V263_World.bind
    (runtime.vector (.capacity 0 k (PV_RunJoin_WorkRange35.width n k) layouts.item)) fun _ =>
    PV_V263_WorkerControl.traverse (step runtime layouts n k callback)
      (PV_V263_Family.indices n k)

theorem length {S A : Type} (runtime : Runtime S) (layouts : Layouts)
    (n k : Nat) (callback : Nat → Q S A) :
    PV_V263_OutputShape.Post
      (fun (values : List A) => values.length = PV_RunJoin_WorkRange35.width n k)
      (run runtime layouts n k callback) := by
  apply PV_V263_OutputShape.bind_any
  intro unit
  simpa only [PV_V263_Family.indices,List.length_range'] using
    PV_V263_OutputShape.traversal_length (step runtime layouts n k callback)
      (PV_V263_Family.indices n k)

/-- A method failure after a callback must retain the callback post-world.
No source Result is fabricated for a native fault. -/
theorem push_fault {S A : Type} (runtime : Runtime S) (layouts : Layouts)
    (n k i : Nat) (callback : Nat → Q S A) (w : State S) (value : A) (e : Fault)
    (hc : (callback i w).outcome = .returned (.ok value))
    (hp : (runtime.vector (.push 0 k (i-PV_RunJoin_WorkRange35.start n k) layouts.item)
      (callback i w).state).outcome = .fault e) :
    (step runtime layouts n k callback i w).outcome = .fault e ∧
    (step runtime layouts n k callback i w).state =
      (runtime.vector (.push 0 k (i-PV_RunJoin_WorkRange35.start n k) layouts.item)
        (callback i w).state).state := by
  simp only [step,PV_V263_World.bind,hc,hp]
  constructor <;> trivial

/-- Fault-free methods do not erase source callback failure or divergence. -/
theorem callback_failure {S A : Type} (runtime : Runtime S) (layouts : Layouts)
    (n k i : Nat) (callback : Nat → Q S A) (w : State S) (e : Error)
    (hc : (callback i w).outcome = .returned (.fail e)) :
    step runtime layouts n k callback i w =
      ⟨.returned (.fail e),(callback i w).state,(callback i w).events⟩ := by
  simp only [step,PV_V263_World.bind,hc]

#print axioms step
#print axioms run
#print axioms length
#print axioms push_fault
#print axioms callback_failure
end R1Z.PV_V263_SourceItems
