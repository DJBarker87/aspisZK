import F3J_Nonvacuity
import F3J_QueryPairs
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_QueryNonvacuity
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation

def calls (state : F3J_QueryPairs.RawState) : Nat → List F3J_QueryPairs.Call
  | 0 => []
  | n+1 => (TranscriptStep.readParts state 1#u8,state)::
      (TranscriptStep.readParts state 2#u8,state)::calls state n

/-- A total concrete source digest inhabits all eight pair witnesses. This
does not claim a jointly accepted native verifier execution. -/
theorem pairs (state : F3J_QueryPairs.RawState) (n : Nat) :
    F3J_QueryPairs.Pairs (F3J_Nonvacuity.digest state) () n state (calls state n) := by
  induction n with
  | zero => exact .nil state
  | succ n ih => exact .cons rfl rfl ih

theorem length (state : F3J_QueryPairs.RawState) (n : Nat) :
    (F3J_QueryPairs.observed (calls state n)).length=2*n := by
  change (List.map _ (calls state n)).length=2*n
  rw [List.length_map]
  induction n with
  | zero => rfl
  | succ n ih => simp only [calls,List.length_cons,ih];omega

#print axioms pairs
#print axioms length
end AspisR1.F3J_QueryNonvacuity
end
