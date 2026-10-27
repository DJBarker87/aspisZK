import PV_B1_PowersBridge
import PV_B1_FieldWideTotal
set_option autoImplicit false
noncomputable section
namespace PV_B1_PowersTotal
open Aeneas Aeneas.Std Result PV_B1_254 PV_B1_PowersControl

-- Result-model totality only; native resource and OS failure obligations remain.
theorem finite_total {N : Usize} (x : W) (fuel : Nat) (out : Array W N) (p : W) (i : Usize)
    (bound : i.val+fuel=N.val) : ∃ result, finite x fuel out p i=ok result := by
  induction fuel generalizing out p i with
  | zero =>
    have hi : ¬ i<N := by change ¬i.val<N.val; omega
    exact ⟨out,by simp only [finite,dispatch,hi,if_false]⟩
  | succ fuel ih =>
    have hi : i<N := by change i.val<N.val; omega
    obtain ⟨old,hr⟩ := PV_B1_ReadTotal.read_total out i hi
    have hm : Array.index_mut_usize out i=ok (old,Aeneas.Std.Array.set out i) := by
      unfold Array.index_mut_usize
      rw [hr]
      rfl
    have hs := PV_B1_PowersBridge.step i hi
    have hn : (Usize.wrapping_add i 1#usize).val+fuel=N.val := by omega
    by_cases more : Usize.wrapping_add i 1#usize<N
    · obtain ⟨next,hnext⟩ := PV_B1_FieldWideTotal.mul p x
      obtain ⟨result,hresult⟩ := ih (Aeneas.Std.Array.set out i p) next (Usize.wrapping_add i 1#usize) hn
      refine ⟨result,?_⟩
      simp only [finite,dispatch,hi,if_true,hm,bind_tc_ok,more,hnext]
      exact hresult
    · obtain ⟨result,hresult⟩ := ih (Aeneas.Std.Array.set out i p) p (Usize.wrapping_add i 1#usize) hn
      refine ⟨result,?_⟩
      simp only [finite,dispatch,hi,if_true,hm,bind_tc_ok,more,if_false]
      exact hresult

theorem total (N : Usize) (x : W) : ∃ result, powers N x=ok result := by
  rw [PV_B1_PowersControl.op254_source]
  exact finite_total x N.val _ _ 0#usize (by change 0+_= _; omega)
#print axioms finite_total
#print axioms total
end PV_B1_PowersTotal
