import NHU_TransitionRange
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.NHU_TransitionReplay
open FIq_Native.pool_v1.pair_forest_semantic_terminal
open NHU_TransitionCut

def fold (p : Public) (carry : Usize) : Nat→R→Result RR
 | 0,_=>ok (.Ok ())
 | n+1,iter=>step p iter carry (fold p carry n)

/-- Bounded replay of the ACTUAL emitted loop, preserving each early Err,
ambient fail and divergence. There is no successful-loop premise. -/
theorem result (p : Public) (carry : Usize) (fuel : Nat) (iter : R)
 (endpoint : iter.end=20#usize) (remaining : iter.start.val+fuel=20) :
 validate_transition_loop p iter carry=fold p carry fuel iter := by
 induction fuel generalizing iter with
 | zero=>
  have start : iter.start=20#usize := UScalar.eq_of_val_eq (by simpa using remaining)
  have same : iter=⟨20#usize,20#usize⟩ := by cases iter;simp_all
  rw [same,NHU_TransitionRange.done,fold]
 | succ n ih=>
  have active : iter.start.val < iter.end.val := by rw [endpoint];change iter.start.val<20;omega
  obtain ⟨next,call,start,finish,assoc⟩:=NHU_TransitionRange.active p iter carry active
  have tail:=ih next (finish.trans endpoint) (by omega)
  rw [assoc,fold,NHU_TransitionStep.association,call,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [tail]
#print axioms result
end AspisR1.NHU_TransitionReplay
end
