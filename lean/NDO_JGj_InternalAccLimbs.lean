import NDO_JGj_InternalAccStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_InternalAccLimbs
open Aeneas Aeneas.Std Result WP FIq_Native
open JGj_RawBounds
theorem source (fuel : Nat) (i : Usize) (a : Raw) (w : Words) (n : Nat)
    (hf : i.val+fuel=4) (hn : n+fuel≤80) (ha : Bound a (n*P)) (hw : Canonical w) :
    ∃ out,state_only_poseidon.internal_linear_lazy_loop0_loop0 a w i=ok out ∧ Bound out ((n+fuel)*P) := by
  induction fuel generalizing i a n with
  | zero =>
    have h : ¬i<4#usize := by scalar_tac
    exact ⟨a,by rw [JGj_InternalAccStep.unfold_loop,if_neg h],by simpa only [Nat.add_zero] using ha⟩
  | succ fuel ih =>
    have h : i<4#usize := by scalar_tac
    obtain ⟨a1,ra,ba⟩ := JGj_InternalAccStep.source a w i n (by change i.val<4;omega) (by omega) ha hw
    have spec : (i+1#usize : Result Usize) ⦃ next=>next.val=i.val+1 ⦄ := by
      apply UScalar.add_spec
      scalar_tac
    obtain ⟨next,rn,vn⟩ := WP.spec_imp_exists spec
    obtain ⟨out,ro,bo⟩ := ih next a1 (n+1) (by omega) (by omega) ba
    have he : (n+1)+fuel=n+(fuel+1) := by omega
    rw [he] at bo
    exact ⟨out,by rw [JGj_InternalAccStep.unfold_loop,if_pos h,ra,bind_tc_ok,rn,bind_tc_ok,ro],bo⟩
#print axioms source
end AspisR1.JGj_InternalAccLimbs
end
