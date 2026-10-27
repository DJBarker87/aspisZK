import R1Z.ProverRwP7CurrentBaseBridge
import R1Z.ProverCommitScalar48
set_option autoImplicit false
namespace R1Z.PV_CB_CanonicalM31
open Aeneas Aeneas.Std Result
abbrev P := AspisCircleGroupOrder.P
/-- Numerical representation invariant from field.rs:21, distinct from lengths. -/
def Valid (word : U32) : Prop := word.val < P

theorem mul (a b : U32) :
    ∃ value, ProverRwP7CurrentBaseBridge.S.mul a b = ok value ∧ Valid value := by
  refine ⟨ProverCommitInverse48.wordMul a b, ?_, ?_⟩
  · rw [ProverRwP7CurrentBaseBridge.mul,ProverCommitInverse48.release_multiply]
  · exact ProverCommitScalar48.word_canonical a b

theorem reduce (input : U64) :
    ∃ value, ProverRwP7CurrentBaseBridge.S.reduce input = ok value ∧ Valid value := by
  obtain ⟨value,hvalue,_,hcanonical⟩ := AspisR1.ExtractedCurrentReducer.current_reduce_mod input
  have checked : AspisR1ProducerChecked47.field.reduce_u64 input = ok value := by
    rw [ProverCommitPrimitive47.reduce,hvalue]
  refine ⟨value,?_,hcanonical⟩
  rw [ProverRwP7CurrentBaseBridge.reduce]
  exact ProverCommitRelease47.reduce input value checked
#print axioms mul
#print axioms reduce
end R1Z.PV_CB_CanonicalM31
