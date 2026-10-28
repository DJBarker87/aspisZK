import NDO_JGj_MatrixGroupTotal
import RPv_FJb_MatrixBlockLoop
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_MatrixLoopTotal
open Aeneas Aeneas.Std Result WP FIq_Native
open FIw_ArrayValue (canonical)
open FJb_MatrixGroupStep (State)
theorem source (n : Nat) (g : Usize) (s : State) (hn : g.val+n=4) (hs : canonical s) :
    ∃ out,state_only_poseidon.external_linear_lazy_loop0 s g=ok out ∧ canonical out := by
  induction n generalizing g s with
  | zero =>
    have h : ¬g<4#usize := by scalar_tac
    exact ⟨s,by rw [state_only_poseidon.external_linear_lazy_loop0.eq_def,if_neg h],hs⟩
  | succ n ih =>
    have hg : g.val<4 := by omega
    obtain ⟨s1,rs,cs⟩ := JGj_MatrixGroupTotal.source s g hg hs
    have spec : (g+1#usize : Result Usize) ⦃ next=>next.val=g.val+1 ⦄ := by
      apply UScalar.add_spec
      scalar_tac
    obtain ⟨next,rn,vn⟩ := WP.spec_imp_exists spec
    obtain ⟨out,ro,co⟩ := ih next s1 (by omega) cs
    exact ⟨out,by rw [FJb_MatrixBlock.unfold_loop s g hg,rs,bind_tc_ok,rn,bind_tc_ok,ro],co⟩
#print axioms source
end AspisR1.JGj_MatrixLoopTotal
end
