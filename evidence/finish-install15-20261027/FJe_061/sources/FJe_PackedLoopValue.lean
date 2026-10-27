import FJe_PackedGroupStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_PackedLoopValue
open Aeneas Aeneas.Std Result WP FIq_Native
open FIw_ArrayValue (canonical decoded)
open FJb_MatrixGroupStep (State)
open FJe_PackedGroupStep (Packed localModel)
/-- Original packed traversal VALUE at every group,with the same state fixed
through all iterations. -/
theorem value (n : Nat) (g : Usize) (s : State) (p out : Packed)
    (hspan : g.val+n=4) (hs : canonical s) (hp : canonical p)
    (run : state_only_poseidon.external_linear_packed_loop s p g=ok out) :
    canonical out ∧ ∀ j : Fin (4#usize).val,decoded out j=
      if g.val≤j.val then localModel s j else decoded p j := by
  induction n generalizing g p with
  | zero =>
    have hno : ¬g<4#usize := by scalar_tac
    rw [FJe_PackedGroupStep.unfold_loop,if_neg hno] at run
    have same : p=out := Result.ok.inj run
    subst out
    refine ⟨hp,?_⟩
    intro j
    have hj : j.val<4 := j.isLt
    rw [if_neg (by omega)]
  | succ n ih =>
    have hg : g.val<4 := by omega
    have hlt : g<4#usize := by scalar_tac
    rw [FJe_PackedGroupStep.unfold_loop,if_pos hlt] at run
    obtain ⟨next,rnext,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨g1,rg1,run⟩ := FIv_Map.bind_success _ _ _ run
    have vn := FJe_PackedGroupStep.value s p next g hg hs hp rnext
    have hspec : (g+1#usize : Result Usize) ⦃z=>z.val=g.val+1⦄ := by
      apply UScalar.add_spec
      scalar_tac
    obtain ⟨g2,rg2,vg⟩ := WP.spec_imp_exists hspec
    have eg : g1=g2 := Result.ok.inj (rg1.symm.trans rg2)
    subst g2
    have rest := ih g1 next (by omega) vn.1 run
    refine ⟨rest.1,?_⟩
    intro j
    have hv := rest.2 j
    simp only [vn.2,Function.update_apply] at hv
    by_cases hj : j.val=g.val
    · have je : j=(⟨g.val,hg⟩ : Fin (4#usize).val) := Fin.ext hj
      subst j
      have hf : ¬g1.val≤g.val := by omega
      simpa only [if_neg hf,↓reduceIte] using hv
    · have je : j≠(⟨g.val,hg⟩ : Fin (4#usize).val) := fun h=>hj (congrArg Fin.val h)
      have he : (g1.val≤j.val) ↔ (g.val≤j.val) := by omega
      simpa only [if_neg je,he] using hv
#print axioms value
end AspisR1.FJe_PackedLoopValue
end
