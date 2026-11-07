import RPz8_SCE_Experiment
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_StateNormalize
open Aeneas Aeneas.Std S2Trust S2W_D189Entry
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open GExq_AccountExperiment SCE_Experiment

/-- Output mapping preserves every query, including repeats and rejected paths. -/
def mapOutput {I V A B : Type} (f : A → B) (p : Program I V A) : Program I V B :=
 bind p (fun x => .done (f x))

theorem eval_map {I V A B : Type} (H : I → V) (f : A → B) (p : Program I V A) :
 eval H (mapOutput f p) = ((eval H p).1, f (eval H p).2) := by
 simp only [mapOutput, eval_bind, eval, List.append_nil]

def firstTop (i : FirstInputs Bool) : FirstInputs Bool := { i with state := true }
def secondTop (i : SecondInputs Bool) : SecondInputs Bool := { i with state := true }

/-- RZ-STATE: allocation success is fixed by the owner-approved top
instantiation. The adaptive second program still receives its actual inputs. -/
def normalize (a : Adversary Bool) : Adversary Bool where
 first := mapOutput firstTop a.first
 second := fun i saved post final => mapOutput secondTop (a.second i saved post final)

theorem first_eval (a : Adversary Bool) (H : Bytes → State) :
 eval H (normalize a).first = ((eval H a.first).1, firstTop (eval H a.first).2) :=
 eval_map H firstTop a.first

theorem second_eval (a : Adversary Bool) (H : Bytes → State)
 (i : FirstInputs Bool) (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : Bool) :
 eval H ((normalize a).second i saved post final) =
 ((eval H (a.second i saved post final)).1, secondTop (eval H (a.second i saved post final)).2) :=
 eval_map H secondTop (a.second i saved post final)

def firstAt (a : Adversary Bool) (H : Bytes → State) : FirstInputs Bool :=
 firstTop (eval H a.first).2

def secondAt (a : Adversary Bool) (H : Bytes → State)
 (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : Bool) : SecondInputs Bool :=
 secondTop (eval H (a.second (firstAt a H) saved post final)).2

/-- The pair comes from the SAME state-normalised adversary at every H.
Realizes is a conclusion, never a predicate filtering worlds. -/
theorem realizes (a : Adversary Bool) (H : Bytes → State)
 (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : Bool) :
 (eval H (normalize a).first).2 = firstAt a H ∧
 (eval H ((normalize a).second (firstAt a H) saved post final)).2 = secondAt a H saved post final := by
 constructor
 · exact congrArg Prod.snd (first_eval a H)
 · exact congrArg Prod.snd (second_eval a H (firstAt a H) saved post final)

theorem states_true (a : Adversary Bool) (H : Bytes → State)
 (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : Bool) :
 (firstAt a H).state = true ∧ (secondAt a H saved post final).state = true := ⟨rfl,rfl⟩

/-- Per-phase query logs are preserved at the same adaptive arguments.
No equality of whole executions with the unnormalised adversary is claimed. -/
theorem logs (a : Adversary Bool) (H : Bytes → State)
 (i : FirstInputs Bool) (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : Bool) :
 (eval H (normalize a).first).1 = (eval H a.first).1 ∧
 (eval H ((normalize a).second i saved post final)).1 = (eval H (a.second i saved post final)).1 := by
 exact ⟨congrArg Prod.fst (first_eval a H), congrArg Prod.fst (second_eval a H i saved post final)⟩

#print axioms eval_map
#print axioms first_eval
#print axioms second_eval
#print axioms realizes
#print axioms states_true
#print axioms logs
end AspisR1.NNH_StateNormalize
