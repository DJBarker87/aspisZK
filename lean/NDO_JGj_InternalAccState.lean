import NDO_JGj_InternalAccLimbs
import NDO_JGj_ExtensionWords
import RPv_JFy_ArrayTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_InternalAccState
open Aeneas Aeneas.Std Result WP FIq_Native
open JGj_RawBounds
open FJb_MatrixGroupStep (State)
theorem source (fuel : Nat) (i : Usize) (s : State) (a : Raw) (n : Nat)
    (hf : i.val+fuel=16) (hn : n+4*fuel≤80) (hs : FIw_ArrayValue.canonical s)
    (ha : Bound a (n*P)) :
    ∃ out,state_only_poseidon.internal_linear_lazy_loop0 s a i=ok out ∧ Bound out ((n+4*fuel)*P) := by
  induction fuel generalizing i a n with
  | zero =>
    have h : ¬i<poseidon2.POSEIDON2_WIDTH := by rw [poseidon2.POSEIDON2_WIDTH];scalar_tac
    exact ⟨a,by rw [state_only_poseidon.internal_linear_lazy_loop0.eq_def,if_neg h],by simpa only [Nat.mul_zero,Nat.add_zero] using ha⟩
  | succ fuel ih =>
    have h : i<poseidon2.POSEIDON2_WIDTH := by rw [poseidon2.POSEIDON2_WIDTH];scalar_tac
    obtain ⟨x,rx,cx⟩ := JFy_ArrayTotal.read s i (by change i.val<16;omega) hs
    have cw := JGj_ExtensionWords.canonical x cx
    obtain ⟨a1,ra,ba⟩ := JGj_InternalAccLimbs.source 4 0#usize a _ n rfl (by omega) ha cw
    have spec : (i+1#usize : Result Usize) ⦃ next=>next.val=i.val+1 ⦄ := by
      apply UScalar.add_spec
      scalar_tac
    obtain ⟨next,rn,vn⟩ := WP.spec_imp_exists spec
    obtain ⟨out,ro,bo⟩ := ih next a1 (n+4) (by omega) (by omega) ba
    have he : (n+4)+4*fuel=n+4*(fuel+1) := by omega
    rw [he] at bo
    refine ⟨out,?_,bo⟩
    rw [state_only_poseidon.internal_linear_lazy_loop0.eq_def,if_pos h,rx,bind_tc_ok]
    change (do
      let a1 ← state_only_poseidon.internal_linear_lazy_loop0_loop0 a (FJb_LimbMap.words x) 0#usize
      let next ← i+1#usize
      state_only_poseidon.internal_linear_lazy_loop0 s a1 next)=ok out
    rw [ra,bind_tc_ok,rn,bind_tc_ok,ro]
#print axioms source
end AspisR1.JGj_InternalAccState
end
