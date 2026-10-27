import FJb_TailStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_TailLoop
open Aeneas Aeneas.Std Result FIq_Native
open FIw_ArrayValue (canonical decoded)
open FJb_MatrixGroupStep (State)
open FJb_ColumnTable (Table)
/-- Complete native final external traversal, keeping the ORIGINAL sum table
fixed and updating each remaining lane exactly once. -/
theorem value (n : Nat) (i : Usize) (s out : State)
    (sums : Table) (hspan : i.val+n=16) (hs : canonical s) (hb : FJb_TailCell.Bounded sums)
    (run : state_only_poseidon.external_linear_lazy_loop1 s sums i=ok out) :
    canonical out ∧ ∀ j : Fin (16#usize).val,decoded out j=
      if i.val≤j.val then decoded s j+FJb_TailStep.columns sums j.val else decoded s j := by
  induction n generalizing i s with
  | zero =>
    have hno : ¬i < poseidon2.POSEIDON2_WIDTH := by rw [poseidon2.POSEIDON2_WIDTH];scalar_tac
    rw [FJb_TailStep.unfold_loop,if_neg hno] at run
    have he : s=out := Result.ok.inj run
    subst out
    refine ⟨hs,?_⟩
    intro j
    have hj : j.val < 16 := j.isLt
    rw [if_neg (by omega)]
  | succ n ih =>
    have hi : i.val < (16#usize).val := by change i.val < 16;omega
    have hlt : i < poseidon2.POSEIDON2_WIDTH := by rw [poseidon2.POSEIDON2_WIDTH];scalar_tac
    rw [FJb_TailStep.unfold_loop,if_pos hlt] at run
    obtain ⟨next,hnext,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨i1,hi1,run⟩ := FIv_Map.bind_success _ _ _ run
    have vn := FJb_TailStep.value s next sums i hi hs hb hnext
    have hspec : (i+1#usize : Result Usize) ⦃z=>z.val=i.val+1⦄ := by
      apply UScalar.add_spec
      scalar_tac
    obtain ⟨i2,hr,vi⟩ := WP.spec_imp_exists hspec
    have he : i1=i2 := Result.ok.inj (hi1.symm.trans hr)
    subst i2
    have rest := ih i1 next (by omega) vn.1 run
    refine ⟨rest.1,?_⟩
    intro j
    have hv := rest.2 j
    simp only [vn.2,Function.update_apply] at hv
    by_cases hj : j.val=i.val
    · have je : j=(⟨i.val,hi⟩ : Fin (16#usize).val) := Fin.ext hj
      subst j
      have hf : ¬i1.val≤i.val := by omega
      have hc : i.val≤i.val := le_refl _
      simpa only [if_neg hf,↓reduceIte,if_pos hc] using hv
    · have je : j≠(⟨i.val,hi⟩ : Fin (16#usize).val) := fun h=>hj (congrArg Fin.val h)
      have hcond : (i1.val≤j.val) ↔ (i.val≤j.val) := by omega
      simpa only [if_neg je,hcond] using hv
#print axioms value
end AspisR1.FJb_TailLoop
end
