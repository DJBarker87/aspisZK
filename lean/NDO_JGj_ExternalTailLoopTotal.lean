import NDO_JGj_ExternalTailStepTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_ExternalTailLoopTotal
open Aeneas Aeneas.Std Result WP FIq_Native
open FIw_ArrayValue (canonical)
open FJb_MatrixGroupStep (State)
theorem source (n : Nat) (i : Usize) (s : State) (sums : FJb_ColumnTable.Table)
    (hn : i.val+n=16) (hs : canonical s) (hb : FJb_TailCell.Bounded sums) :
    ∃ out,state_only_poseidon.external_linear_lazy_loop1 s sums i=ok out ∧ canonical out := by
  induction n generalizing i s with
  | zero =>
    have h : ¬i<poseidon2.POSEIDON2_WIDTH := by rw [poseidon2.POSEIDON2_WIDTH];scalar_tac
    exact ⟨s,by rw [FJb_TailStep.unfold_loop,if_neg h],hs⟩
  | succ n ih =>
    have h : i<poseidon2.POSEIDON2_WIDTH := by rw [poseidon2.POSEIDON2_WIDTH];scalar_tac
    obtain ⟨s1,rs,cs⟩ := JGj_ExternalTailStepTotal.source s sums i (by omega) hs hb
    have spec : (i+1#usize : Result Usize) ⦃ next=>next.val=i.val+1 ⦄ := by
      apply UScalar.add_spec
      scalar_tac
    obtain ⟨next,rn,vn⟩ := WP.spec_imp_exists spec
    obtain ⟨out,ro,co⟩ := ih next s1 (by omega) cs
    exact ⟨out,by rw [FJb_TailStep.unfold_loop,if_pos h,rs,bind_tc_ok,rn,bind_tc_ok,ro],co⟩
#print axioms source
end AspisR1.JGj_ExternalTailLoopTotal
end
