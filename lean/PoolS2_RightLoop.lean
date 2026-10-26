import PoolS2_RightSuffix
import PoolS2_Index
set_option autoImplicit false
namespace AspisR1.PoolS2_RightLoop
open Aeneas Aeneas.Std Result ControlFlow WP PoolS2_RightSuffix PoolS2_RightStep

def Inv (keys : Slice Key) (root : Key) (target : Bool) (s : Usize × Bool) : Prop :=
  s.1.val ≤ keys.val.length ∧ remaining keys root s.1.val s.2 = target

theorem exact (keys : Slice Key) (root : Key) (left i : Usize) (equal : Bool)
    (readLeft : Slice.index_usize keys left = ok root) (bound : i.val ≤ keys.val.length) :
    PoolS2_Unique.right_unique_loop keys left i equal = ok (remaining keys root i.val equal) := by
  let target := remaining keys root i.val equal
  have h : WP.spec (PoolS2_Unique.right_unique_loop keys left i equal) (fun out => out = target) := by
    unfold PoolS2_Unique.right_unique_loop
    refine loop.spec_decr_nat
      (fun s : Usize × Bool => keys.val.length - s.1.val)
      (Inv keys root target) (fun out : Bool => out = target)
      (fun (j,e) => PoolS2_Unique.right_unique_loop.body keys left j e)
      (i,equal) ?_ ⟨bound,rfl⟩
    rintro ⟨j,e⟩ ⟨range,eq⟩
    dsimp only at range eq ⊢
    by_cases more : j < Slice.len keys
    · cases e with
      | false =>
        rw [PoolS2_RightStep.stopped]
        change false = target
        simpa [remaining] using eq
      | true =>
        have va : j.val < keys.val.length := by scalar_tac
        rw [PoolS2_RightStep.step keys left j root _ more readLeft (PoolS2_Index.read keys j va)]
        change (Inv keys root target (Usize.wrapping_add j 1#usize,_) ∧
          keys.val.length - (Usize.wrapping_add j 1#usize).val < keys.val.length - j.val)
        have inc := PoolS2_Index.increment keys j more
        refine ⟨⟨?_,?_⟩,?_⟩
        · simp only [inc]; omega
        · change remaining keys root (Usize.wrapping_add j 1#usize).val _ = target
          rw [inc]
          have nx := PoolS2_RightSuffix.next keys root j.val true va
          simpa only [Bool.true_and] using nx.symm.trans eq
        · simp only [inc]; omega
    · rw [PoolS2_RightStep.ended keys left j e more]
      change e = target
      have done := PoolS2_RightSuffix.ended keys root j.val e (by scalar_tac)
      exact done.symm.trans eq
  cases run : PoolS2_Unique.right_unique_loop keys left i equal with
  | fail err => simp only [run,WP.spec,WP.theta] at h
  | div => simp only [run,WP.spec,WP.theta] at h
  | ok out =>
    simp only [run,WP.spec,WP.theta,WP.wp_return] at h
    rw [h]

#print axioms exact
end AspisR1.PoolS2_RightLoop
