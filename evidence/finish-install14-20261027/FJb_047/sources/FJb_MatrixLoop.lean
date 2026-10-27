import FJb_MatrixModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_MatrixLoop
open Aeneas Aeneas.Std Result FIq_Native
open FIw_ArrayValue (canonical decoded)
open FJb_MatrixGroupStep (State)
/-- Complete native first external traversal, with one symbolic step per group. -/
theorem value (n : Nat) (g : Usize) (s out : State)
    (hspan : g.val+n=4) (hs : canonical s)
    (run : state_only_poseidon.external_linear_lazy_loop0 s g=ok out) :
    canonical out ∧ decoded out=FJb_MatrixModel.fold n g.val (decoded s) := by
  induction n generalizing g s with
  | zero =>
    rw [state_only_poseidon.external_linear_lazy_loop0.eq_def] at run
    have hg : ¬g < 4#usize := by scalar_tac
    rw [if_neg hg] at run
    have he : s=out := Result.ok.inj run
    subst out
    exact ⟨hs,rfl⟩
  | succ n ih =>
    have hg : g.val < 4 := by omega
    rw [FJb_MatrixBlock.unfold_loop s g hg] at run
    obtain ⟨next,hnext,run⟩ := FIv_Map.bind_success _ _ _ run
    obtain ⟨g1,hg1,run⟩ := FIv_Map.bind_success _ _ _ run
    have v := FJb_MatrixBlock.value s next g hg hs hnext
    have hspec : (g+1#usize : Result Usize) ⦃z=>z.val=g.val+1⦄ := by
      apply UScalar.add_spec
      scalar_tac
    obtain ⟨g2,hr,hv⟩ := WP.spec_imp_exists hspec
    have he : g1=g2 := Result.ok.inj (hg1.symm.trans hr)
    subst g2
    have rest := ih g1 next (by omega) v.1 run
    refine ⟨rest.1,?_⟩
    rw [rest.2,v.2,FJb_MatrixModel.model,hv]
    rfl
#print axioms value
end AspisR1.FJb_MatrixLoop
end
