import PoolS2_KeySuffix
import PoolS2_Index
set_option autoImplicit false
namespace AspisR1.PoolS2_KeyLoop
open Aeneas Aeneas.Std Result ControlFlow WP PoolS2_KeySuffix

def Inv (a b : Slice U8) (target : Bool) (s : Usize × Bool) : Prop :=
  s.1.val ≤ a.val.length ∧ remaining a b s.1.val s.2 = target

theorem exact (a b : Slice U8) (i : Usize) (equal : Bool)
    (same : a.val.length = b.val.length) (bound : i.val ≤ a.val.length) :
    PoolS2_Unique.key_equal_loop a b i equal = ok (remaining a b i.val equal) := by
  let target := remaining a b i.val equal
  have h : WP.spec (PoolS2_Unique.key_equal_loop a b i equal) (fun out => out = target) := by
    unfold PoolS2_Unique.key_equal_loop
    refine loop.spec_decr_nat
      (fun s : Usize × Bool => a.val.length - s.1.val)
      (Inv a b target) (fun out : Bool => out = target)
      (fun (j,e) => PoolS2_Unique.key_equal_loop.body a b j e)
      (i,equal) ?_ ⟨bound,rfl⟩
    rintro ⟨j,e⟩ ⟨range,eq⟩
    dsimp only at range eq ⊢
    by_cases more : j < Slice.len a
    · cases e with
      | false =>
        rw [PoolS2_KeyStep.stopped]
        change false = target
        simpa [remaining] using eq
      | true =>
        have va : j.val < a.val.length := by scalar_tac
        have vb : j.val < b.val.length := by omega
        rw [PoolS2_KeyStep.step a b j _ _ more (PoolS2_Index.read a j va) (PoolS2_Index.read b j vb)]
        change (Inv a b target (Usize.wrapping_add j 1#usize,_) ∧
          a.val.length - (Usize.wrapping_add j 1#usize).val < a.val.length - j.val)
        have inc := PoolS2_Index.increment a j more
        refine ⟨⟨?_,?_⟩,?_⟩
        · simp only [inc]; omega
        · change remaining a b (Usize.wrapping_add j 1#usize).val _ = target
          rw [inc]
          have nx := PoolS2_KeySuffix.next a b j.val true va vb
          simpa only [Bool.true_and] using nx.symm.trans eq
        · simp only [inc]; omega
    · rw [PoolS2_KeyStep.ended a b j e more]
      change e = target
      have done := PoolS2_KeySuffix.ended a b j.val e (by scalar_tac)
      exact done.symm.trans eq
  cases run : PoolS2_Unique.key_equal_loop a b i equal with
  | fail err => simp only [run,WP.spec,WP.theta] at h
  | div => simp only [run,WP.spec,WP.theta] at h
  | ok out =>
    simp only [run,WP.spec,WP.theta,WP.wp_return] at h
    rw [h]

#print axioms exact
end AspisR1.PoolS2_KeyLoop
