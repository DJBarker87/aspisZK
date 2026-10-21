import Mathlib.Data.List.Range
import Lean.Elab.Tactic.Omega

/-! Explicit finite-loop contract for the source/reference P6 correspondence.
This does not assume that a native test is a Lean proof of a source step. -/
set_option autoImplicit false
namespace S7OwnedP6LoopSimulation

def run {S : Type} (step : Nat → S → S) : Nat → Nat → S → S
  | 0, _, state => state
  | fuel+1, index, state => run step fuel (index+1) (step index state)

/-- A relation preserving the ordinal and full loop state composes across
all rows. The per-step condition remains visible until separately certified. -/
theorem simulation {S T : Type} (source : Nat → S → S) (reference : Nat → T → T)
    (relation : Nat → S → T → Prop) (start count : Nat) (a : S) (b : T)
    (initial : relation start a b)
    (step : ∀ i, start ≤ i → i < start+count → ∀ x y,
      relation i x y → relation (i+1) (source i x) (reference i y)) :
    relation (start+count) (run source count start a) (run reference count start b) := by
  induction count generalizing start a b with
  | zero => simpa only [run,Nat.add_zero] using initial
  | succ count ih =>
    have first := step start (by omega) (by omega) a b initial
    have rest : ∀ i, start+1 ≤ i → i < (start+1)+count → ∀ x y,
        relation i x y → relation (i+1) (source i x) (reference i y) := by
      intro i hlo hhi x y hxy
      exact step i (by omega) (by omega) x y hxy
    simpa only [run,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      ih (start+1) (source start a) (reference start b) first rest

/-- The source subtraction selects the ordinal of the just-constructed table
record, including stage 2's nonzero start. -/
theorem query_ordinal (start ordinal count : Nat) (h : ordinal<count) :
    (start+ordinal)-start=ordinal ∧ start+ordinal<start+count ∧
      5*((start+ordinal)-start)+4<5*count := by omega

#print axioms simulation
#print axioms query_ordinal
end S7OwnedP6LoopSimulation
