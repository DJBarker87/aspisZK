import R1Z.ProverCommitGammaCell53
import R1Z.ProverCommitWideArray48
import R1Z.ProverCommitArray49
/-! Full gamma batching interval induction over stored coefficient columns.
The source gamma-power array is immutable and every other output slot is preserved. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitGammaFill53
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47
open ProverCommitWideOps48 ProverCommitMix48 ProverCommitGammaCell53

attribute [local irreducible] table sourceArray source value

theorem fill (c : Nat → Nat → Raw) (hc : ∀ l, l<29 → ∀ j, j<1024 → canonical (c l j))
    (p : Nat → Raw) (hp : ∀ l, l<29 → canonical (p l)) (n : Nat) (xs : Nat → Raw)
    (hxs : ∀ i, i<1024 → canonical (xs i))
    (j : Usize) (left : U16) (hleft : left.val=n) (bound : j.val+n≤1024) :
    ∃ out : Nat → Raw,
      gamma53.fill (table c) (sourceArray 29#usize p) (sourceArray 1024#usize xs) j left=
        ok (sourceArray 1024#usize out) ∧
      (∀ i, i<1024 → canonical (out i)) ∧
      ∀ i, i<1024 → value (out i)=
        if j.val ≤ i ∧ i<j.val+n then ProverCommitMix48.sum (fun l => c l i) p 29 0 else value (xs i) := by
  induction n generalizing xs j left with
  | zero =>
    have hz : left=0#u16 := by scalar_tac
    refine ⟨xs,?_,hxs,?_⟩
    · rw [gamma53.fill,hz];rfl
    · intro i hi;rw [if_neg (by omega)]
  | succ n ih =>
    have hn : left≠0#u16 := by scalar_tac
    have hj : j.val<1024 := by omega
    have hdec : (U16.wrapping_sub left 1#u16).val=n := by
      rw [ProverCommitPairCounter47.sub_one left (by omega)];omega
    have hinc : (Usize.wrapping_add j 1#usize).val=j.val+1 :=
      ProverCommitPairCounter47.next_val j (by omega)
    obtain ⟨v,hcell,hcv,hdv⟩ := ProverCommitGammaCell53.exact_result c p hc hp j hj
    let changed := Function.update xs j.val v
    have hc : ∀ i, i<1024 → canonical (changed i) := by
      intro i hi
      by_cases he : i=j.val
      · subst i;simpa only [changed,Function.update_self] using hcv
      · simpa only [changed,Function.update_of_ne he] using hxs i hi
    obtain ⟨out,hout,hcout,hdout⟩ := ih changed hc _ _ hdec (by rw [hinc];omega)
    refine ⟨out,?_,hcout,?_⟩
    · rw [gamma53.fill]
      simp only [hn,if_false,hcell,bind_tc_ok]
      rw [ProverCommitWideArray48.update _ _ _ hj v]
      simp only [lift,bind_tc_ok]
      exact hout
    · intro i hi
      rw [hdout i hi,hinc]
      by_cases he : i=j.val
      · subst i
        rw [if_neg (by omega),if_pos (by omega)]
        simpa only [changed,Function.update_self,show (0#usize).val=0 from rfl] using hdv
      · by_cases ht : j.val+1 ≤ i ∧ i<j.val+1+n
        · rw [if_pos ht,if_pos (by omega)]
        · rw [if_neg ht,if_neg (by omega)]
          simp only [changed,Function.update_of_ne he]

#print axioms fill
end R1Z.ProverCommitGammaFill53
