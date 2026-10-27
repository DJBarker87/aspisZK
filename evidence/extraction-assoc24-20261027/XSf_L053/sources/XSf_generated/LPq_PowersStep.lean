import LPq_WidePorts
import XRy_PowersStep
set_option autoImplicit false
namespace AspisR1.LPq_PowersStep
open Aeneas Aeneas.Std Result ControlFlow LPi_FieldValues LPq_FieldPorts XRo_Join_Carriers
abbrev port (x : NE) := XRy_LoopWide.toLoop (wide x)

theorem step {N : Usize} (x p : NE) (a : Array NE N) (i : Usize)
    (hi : i.val<N.val) (hx : canonE x) (hp : canonE p) :
    ∃ i', i'.val=i.val+1 ∧
      ((i'=N ∧ FIo_Native.weights.powers_loop.body x a p i=ok (.done (a.set i p)) ∧
        AspisR1LoopPowers.weights.early_powers_loop.body (port x) (arr port a) (port p) i=
          ok (.done (arr port (a.set i p)))) ∨
       (i'≠N ∧ ∃ p', canonE p' ∧
        FIo_Native.weights.powers_loop.body x a p i=ok (.cont (a.set i p,p',i')) ∧
        AspisR1LoopPowers.weights.early_powers_loop.body (port x) (arr port a) (port p) i=
          ok (.cont (arr port (a.set i p),port p',i')))) := by
  obtain ⟨old,hm⟩ := XRy_PowersStep.mutable a i hi
  obtain ⟨old',hm'⟩ := XRy_PowersStep.mutable (arr port a) i hi
  have hN : N.val ≤ Usize.max := by scalar_tac
  have hAdd : (i+1#usize : Result Usize) ⦃ j => j.val=i.val+1 ⦄ := by
    apply UScalar.add_spec
    have hone : (1#usize).val=1 := by scalar_tac
    simpa only [hone,UScalar.max_USize_eq] using (show i.val+1 ≤ Usize.max by omega)
  obtain ⟨i',ei,vi⟩ := WP.spec_imp_exists hAdd
  have wi : Usize.wrapping_add i 1#usize=i' := by
    apply UScalar.eq_of_val_eq
    rw [Usize.wrapping_add_val_eq]
    have hn : N.val < UScalar.size .Usize := by
      simpa only [UScalar.size,UScalar.val,UScalarTy.numBits] using N.bv.isLt
    change (i.val+1)%UScalar.size .Usize=i'.val
    rw [Nat.mod_eq_of_lt (by omega)]
    exact vi.symm
  have hlt : i<N := by scalar_tac
  refine ⟨i',vi,?_⟩
  by_cases he : i'=N
  · left
    refine ⟨he,?_,?_⟩
    · simp only [FIo_Native.weights.powers_loop.body,if_pos hlt,hm,lift,bind_tc_ok,wi,he,↓reduceIte]
      rfl
    · simp only [AspisR1LoopPowers.weights.early_powers_loop.body,if_pos hlt,hm',ei,
        bind_tc_ok,he,↓reduceIte,XRy_ArrayMap.set]
      rfl
  · right
    obtain ⟨p',ep,hp',tp⟩ := LPq_WidePorts.loop_mul p x hp hx
    refine ⟨he,p',hp',?_,?_⟩
    · simp only [FIo_Native.weights.powers_loop.body,if_pos hlt,hm,lift,bind_tc_ok,wi,if_neg he,ep]
      rfl
    · simp only [AspisR1LoopPowers.weights.early_powers_loop.body,if_pos hlt,hm',ei,
        bind_tc_ok,if_neg he,tp,XRy_ArrayMap.set]
      rfl

#print axioms step
end AspisR1.LPq_PowersStep
