import R1Z.ProverCommitArrayValue47
import R1Z.ProverCommitBasisCounter47
/-! Exact interval update for one source-owned natural-basis block. -/
set_option autoImplicit false
namespace R1Z.ProverCommitBasisFillValue47
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47 ProverCommitNativeOps47
open ProverCommitPairCounter47 ProverCommitBasisCounter47
open AspisR1.ExtractedCurrentQM31Exact
attribute [local irreducible] sourceArray fillN

theorem add_val (a b : Usize) (h : a.val+b.val<2048) :
    (Usize.wrapping_add a b).val=a.val+b.val := by
  rw [Usize.wrapping_add_val_eq]
  exact Nat.mod_eq_of_lt (by have := usize_large;omega)

theorem fill_value (n : Nat) (xs : Nat → Old.Q)
    (hxs : ∀ k, k<512 → Canonical (xs k)) (j width : Usize)
    (bound : j.val+n≤width.val) (capacity : 2*width.val≤512)
    (factor : Old.Q) (hfactor : Canonical factor) :
    ∃ ys : Nat → Old.Q,
      fillN n (sourceArray 512#usize xs) j width (ProverCommitNativeOps47.embedded factor) =
        ok (sourceArray 512#usize ys) ∧
      (∀ k, k<512 → Canonical (ys k)) ∧
      ∀ k, k<512 → decode (ys k) =
        if width.val+j.val≤k ∧ k<width.val+j.val+n then
          decode (xs (k-width.val))*decode factor else decode (xs k) := by
  induction n generalizing xs j with
  | zero =>
    refine ⟨xs,by rw [fillN],hxs,?_⟩
    intro k hk
    rw [if_neg (by omega)]
  | succ n ih =>
    have hj : j.val<512 := by omega
    have hd : (Usize.wrapping_add width j).val=width.val+j.val :=
      add_val _ _ (by omega)
    have hn : (Usize.wrapping_add j 1#usize).val=j.val+1 := next_val _ (by omega)
    obtain ⟨p,hp,hcp,hdp⟩ := ProverCommitNativeOps47.mul_exact (xs j.val) factor (hxs _ hj) hfactor
    let next : Nat → Old.Q := Function.update xs (width.val+j.val) p
    have hnext : ∀ k, k<512 → Canonical (next k) := by
      intro k hk
      by_cases he : k=width.val+j.val
      · subst k
        simpa only [next,Function.update_self] using hcp
      · simpa only [next,Function.update_of_ne he] using hxs k hk
    obtain ⟨ys,hy,hcy,hval⟩ := ih next hnext (Usize.wrapping_add j 1#usize)
      (by rw [hn];omega)
    refine ⟨ys,?_,hcy,?_⟩
    · rw [fillN,index _ _ j (by exact hj)]
      simp only [bind_tc_ok,hp]
      rw [ProverCommitArrayValue47.update _ _ (Usize.wrapping_add width j)
        (by change (Usize.wrapping_add width j).val<512;rw [hd];omega),hd]
      simp only [bind_tc_ok]
      exact hy
    · intro k hk
      rw [hval k hk,hn]
      change (if width.val+(j.val+1)≤k ∧ k<width.val+(j.val+1)+n then
        decode (next (k-width.val))*decode factor else decode (next k)) = _
      by_cases he : k=width.val+j.val
      · have htail : ¬ (width.val+(j.val+1)≤k ∧ k<width.val+(j.val+1)+n) := by omega
        have hall : width.val+j.val≤k ∧ k<width.val+j.val+(n+1) := by omega
        rw [if_neg htail,if_pos hall]
        simp only [next,he,Function.update_self]
        rw [hdp,Nat.add_sub_cancel_left]
      · by_cases ht : width.val+(j.val+1)≤k ∧ k<width.val+(j.val+1)+n
        · have hall : width.val+j.val≤k ∧ k<width.val+j.val+(n+1) := by omega
          have hl : k-width.val≠width.val+j.val := by omega
          rw [if_pos ht,if_pos hall]
          simp only [next,Function.update_of_ne hl]
        · have hall : ¬ (width.val+j.val≤k ∧ k<width.val+j.val+(n+1)) := by omega
          rw [if_neg ht,if_neg hall]
          simp only [next,Function.update_of_ne he]

#print axioms add_val
#print axioms fill_value
end R1Z.ProverCommitBasisFillValue47
