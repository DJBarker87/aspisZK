import NDO_JGj_ThreeStepTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_ThreeLoopTotal
open Aeneas Aeneas.Std Result WP FIq_Native
open FIw_ArrayValue (canonical)
open FJb_MatrixGroupStep (State)
open FJe_ThreeColumnStep (Weights)
open FJb_M31Step (Constants Bounded)
theorem source (n : Nat) (i : Usize) (s : State) (w : Weights) (c0 c1 c2 : Constants)
    (hn : i.val+n=16) (hs : canonical s) (hw : canonical w) (h0 : Bounded c0) (h1 : Bounded c1) (h2 : Bounded c2) :
    ∃ out,state_only_poseidon.interpolate_three_constant_columns_loop w c0 c1 c2 s i=ok out ∧ canonical out := by
  induction n generalizing i s with
  | zero =>
    have h : ¬i<poseidon2.POSEIDON2_WIDTH := by rw [poseidon2.POSEIDON2_WIDTH];scalar_tac
    exact ⟨s,by rw [FJe_ThreeColumnStep.unfold_loop,if_neg h],hs⟩
  | succ n ih =>
    have h : i<poseidon2.POSEIDON2_WIDTH := by rw [poseidon2.POSEIDON2_WIDTH];scalar_tac
    obtain ⟨s1,rs,cs⟩ := JGj_ThreeStepTotal.source w c0 c1 c2 s i (by change i.val<16;omega) hw h0 h1 h2 hs
    have spec : (i+1#usize : Result Usize) ⦃ next=>next.val=i.val+1 ⦄ := by
      apply UScalar.add_spec
      scalar_tac
    obtain ⟨next,rn,vn⟩ := WP.spec_imp_exists spec
    obtain ⟨out,ro,co⟩ := ih next s1 (by omega) cs
    exact ⟨out,by rw [FJe_ThreeColumnStep.unfold_loop,if_pos h,rs,bind_tc_ok,rn,bind_tc_ok,ro],co⟩
#print axioms source
end AspisR1.JGj_ThreeLoopTotal
end
