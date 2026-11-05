import NHU_TransitionGuardValue
import NHU_TransitionReplay
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.NHU_TransitionLoopTotal
open FIq_Native.pool_v1.pair_forest_semantic_terminal
open NHU_TransitionCut

theorem result (p : Public) (carry : Usize) (fuel : Nat) (iter : R)
 (endpoint : iter.end=20#usize) (remaining : iter.start.val+fuel=20) :
 ∃ status,validate_transition_loop p iter carry=ok status := by
 induction fuel generalizing iter with
 | zero=>
  have start : iter.start=20#usize := UScalar.eq_of_val_eq (by simpa using remaining)
  have same : iter=⟨20#usize,20#usize⟩ := by cases iter;simp_all
  exact ⟨.Ok (),by rw [same];exact NHU_TransitionRange.done p carry⟩
 | succ n ih=>
  have active : iter.start.val < iter.end.val := by rw [endpoint];change iter.start.val<20;omega
  have bound : iter.start.val<20 := by rw [endpoint] at active;exact active
  obtain ⟨next,_,start,finish,assoc⟩:=NHU_TransitionRange.active p iter carry active
  obtain ⟨last,tail⟩:=ih next (finish.trans endpoint) (by omega)
  obtain ⟨front,guardCall⟩:=NHU_TransitionGuardValue.total p iter.start carry bound
  rw [assoc,NHU_TransitionGuard.association,guardCall]
  cases front with
  | Ok unit=>exact ⟨last,by cases unit;exact tail⟩
  | Err error=>exact ⟨.Err error,rfl⟩

theorem start (p : Public) (carry : Usize) :
 ∃ status,validate_transition_loop p ⟨0#usize,20#usize⟩ carry=ok status :=
 result p carry 20 ⟨0#usize,20#usize⟩ rfl rfl
#print axioms result
#print axioms start
end AspisR1.NHU_TransitionLoopTotal
end
