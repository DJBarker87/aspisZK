import PoolS2_UniqueSuffix
import PoolS2_UniqueStep
import PoolS2_Index
set_option autoImplicit false
namespace AspisR1.PoolS2_UniqueLoop
open Aeneas Aeneas.Std Result ControlFlow WP PoolS2_UniqueSuffix PoolS2_RightStep

def Inv (keys : Slice Key) (target : Bool) (s : Usize × Bool) : Prop :=
  s.1.val ≤ keys.val.length ∧ remaining keys s.1.val s.2 = target

theorem exact (keys : Slice Key) (i : Usize) (equal : Bool)
    (bound : i.val ≤ keys.val.length) :
    PoolS2_Unique.unique_keys_loop keys i equal = ok (remaining keys i.val equal) := by
  let target := remaining keys i.val equal
  have h : WP.spec (PoolS2_Unique.unique_keys_loop keys i equal) (fun out => out = target) := by
    unfold PoolS2_Unique.unique_keys_loop
    refine loop.spec_decr_nat
      (fun s : Usize × Bool => keys.val.length - s.1.val)
      (Inv keys target) (fun out : Bool => out = target)
      (fun (j,e) => PoolS2_Unique.unique_keys_loop.body keys j e)
      (i,equal) ?_ ⟨bound,rfl⟩
    rintro ⟨j,e⟩ ⟨range,eq⟩
    dsimp only at range eq ⊢
    by_cases more : j < Slice.len keys
    · cases e with
      | false =>
        rw [PoolS2_UniqueStep.stopped]
        change false = target
        simpa [remaining] using eq
      | true =>
        have va : j.val < keys.val.length := by scalar_tac
        rw [PoolS2_UniqueStep.step keys j va]
        change (Inv keys target (Usize.wrapping_add j 1#usize,_) ∧
          keys.val.length - (Usize.wrapping_add j 1#usize).val < keys.val.length - j.val)
        have inc := PoolS2_Index.increment keys j more
        refine ⟨⟨?_,?_⟩,?_⟩
        · simp only [inc]; omega
        · change remaining keys (Usize.wrapping_add j 1#usize).val _ = target
          rw [inc]
          have nx := PoolS2_UniqueSuffix.next keys j.val true va
          simpa only [Bool.true_and] using nx.symm.trans eq
        · simp only [inc]; omega
    · rw [PoolS2_UniqueStep.ended keys j e more]
      change e = target
      have done := PoolS2_UniqueSuffix.ended keys j.val e (by scalar_tac)
      exact done.symm.trans eq
  cases run : PoolS2_Unique.unique_keys_loop keys i equal with
  | fail err => simp only [run,WP.spec,WP.theta] at h
  | div => simp only [run,WP.spec,WP.theta] at h
  | ok out =>
    simp only [run,WP.spec,WP.theta,WP.wp_return] at h
    rw [h]

#print axioms exact
end AspisR1.PoolS2_UniqueLoop
