import R1Z.ProverCommitM31Array48
import R1Z.ProverCommitQArray48
import R1Z.ProverCommitScalar48
import R1Z.ProverCommitInterpolationIndices48
/-! Complete owned coefficient accumulator, with interval value and canonicality
invariants. No concrete 28-cell computation is reduced. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitInterpolationAccumulate48
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open ProverCommitInterpolationIndices48
open AspisR1.ExtractedCurrentQM31Exact (decode)
attribute [local irreducible] ProverCommitQArray48.array ProverCommitM31Array48.array

theorem accumulate_value (n : Nat) (xs : Nat → Old.Q)
    (hxs : ∀ j, j < 28 → Canonical (xs j)) (basis : Nat → U32) (scale : Old.Q)
    (k left : U8) (hleft : left.val=n) (bound : k.val+n ≤ 28) :
    ∃ ys : Nat → Old.Q,
      accumulate (ProverCommitQArray48.array 28#usize xs)
          (ProverCommitM31Array48.array 28#usize basis)
          (ProverCommitNativeQ48.source scale) k left=ok (ProverCommitQArray48.array 28#usize ys) ∧
      (∀ j, j < 28 → Canonical (ys j)) ∧
      ∀ j, j < 28 → decode (ys j)=decode (xs j)+
        if k.val ≤ j ∧ j < k.val+n then decode scale*ProverCommitScalar48.embed (basis j) else 0 := by
  induction n generalizing xs k left with
  | zero =>
    have hz : left=0#u8 := by scalar_tac
    refine ⟨xs,?_,hxs,?_⟩
    · rw [accumulate,hz];rfl
    · intro j hj
      rw [if_neg (by omega),add_zero]
  | succ n ih =>
    have hn : left≠0#u8 := by scalar_tac
    have hk : k.val < 28 := by omega
    have hcast : (UScalar.cast .Usize k).val=k.val := by scalar_tac
    have hnext : (U8.wrapping_add k 1#u8).val=k.val+1 := next_val k hk
    have hdec : (U8.wrapping_sub left 1#u8).val=n := by
      rw [ProverCommitBasisCounter47.sub_one left (by omega)];omega
    obtain ⟨hprod,hcprod,hdprod⟩ := ProverCommitScalar48.source_exact scale (basis k.val)
    obtain ⟨z,hz,hcz,hdz⟩ := ProverCommitNativeQ48.add (xs k.val)
      (ProverCommitScalar48.product scale (basis k.val)) (hxs _ hk) hcprod
    let next := Function.update xs k.val z
    have hcnext : ∀ j, j < 28 → Canonical (next j) := by
      intro j hj
      by_cases he : j=k.val
      · subst j;simp only [next,Function.update_self];exact hcz
      · simp only [next,Function.update_of_ne he];exact hxs j hj
    obtain ⟨ys,hy,hcy,hdy⟩ := ih next hcnext (U8.wrapping_add k 1#u8)
      (U8.wrapping_sub left 1#u8) hdec (by rw [hnext];omega)
    refine ⟨ys,?_,hcy,?_⟩
    · rw [accumulate]
      simp only [hn,if_false,lift,bind_tc_ok]
      rw [ProverCommitQArray48.index _ _ _ (by rw [hcast];exact hk)]
      rw [ProverCommitM31Array48.index _ _ _ (by rw [hcast];exact hk)]
      simp only [hcast,hprod,hz,bind_tc_ok]
      rw [ProverCommitQArray48.update _ _ _ (by rw [hcast];exact hk)]
      simp only [hcast,bind_tc_ok]
      exact hy
    · intro j hj
      rw [hdy j hj,hnext]
      by_cases he : j=k.val
      · subst j
        simp only [next,Function.update_self,hdz,hdprod,if_neg (by omega : ¬(k.val+1 ≤ k.val ∧ k.val < k.val+1+n)),add_zero,
          if_pos (by omega : k.val ≤ k.val ∧ k.val < k.val+(n+1))]
      · simp only [next,Function.update_of_ne he]
        by_cases hinside : k.val+1 ≤ j ∧ j < k.val+1+n
        · rw [if_pos hinside,if_pos (by omega)]
        · rw [if_neg hinside,if_neg (by omega)]

#print axioms accumulate_value
end R1Z.ProverCommitInterpolationAccumulate48
