-- Inherited body, import-only deployed-cohort retarget.
import NCD_B_LPi_TowerValues
set_option autoImplicit false
namespace AspisR1.LPi_PowersStep
open Aeneas Aeneas.Std Result ControlFlow LPi_FieldValues

theorem step {N : Usize} (x p : NE) (a : Array NE N) (i : Usize)
    (hi : i.val<N.val) (hx : canonE x) (hp : canonE p) :
    ∃ i', i'.val=i.val+1 ∧
      ((i'=N ∧ FIo_Native.weights.powers_loop.body x a p i=ok (.done (a.set i p))) ∨
       (i'≠N ∧ ∃ p', FIo_Native.weights.powers_loop.body x a p i=
         ok (.cont (a.set i p,p',i')) ∧ canonE p' ∧ ew p'=mulE (ew p) (ew x))) := by
  obtain ⟨out,hmut,hspec⟩ := WP.spec_imp_exists
    (Array.index_mut_usize_spec a i (by simpa [a.property] using hi))
  rcases out with ⟨old,back⟩
  rcases hspec with ⟨_,hback⟩
  subst back
  let i' := Usize.wrapping_add i 1#usize
  have inc : i'.val=i.val+1 := by
    rw [Usize.wrapping_add_val_eq]
    apply Nat.mod_eq_of_lt
    have hN : N.val < UScalar.size .Usize := by
      simpa only [UScalar.size,UScalar.val,UScalarTy.numBits] using N.bv.isLt
    change i.val+1 < UScalar.size .Usize
    omega
  have hlt : i<N := by scalar_tac
  refine ⟨i',inc,?_⟩
  by_cases he : i'=N
  · refine Or.inl ⟨he,?_⟩
    simp only [FIo_Native.weights.powers_loop.body,hlt,ite_true,
      hmut,lift,bind_tc_ok,show Usize.wrapping_add i 1#usize=i' from rfl,he]
    rfl
  · obtain ⟨p',hm,hc,hv⟩ := LPi_TowerValues.wide_mul p x hp hx
    refine Or.inr ⟨he,p',?_,hc,hv⟩
    simp only [FIo_Native.weights.powers_loop.body,hlt,ite_true,hmut,lift,bind_tc_ok,
      show Usize.wrapping_add i 1#usize=i' from rfl,he,ite_false,hm]
    rfl

theorem done {N : Usize} (x p : NE) (a : Array NE N) (i : Usize)
    (hi : N.val ≤ i.val) : FIo_Native.weights.powers_loop.body x a p i=ok (.done a) := by
  have hn : ¬i<N := by scalar_tac
  simp only [FIo_Native.weights.powers_loop.body,hn,ite_false]

#print axioms step
#print axioms done
end AspisR1.LPi_PowersStep
