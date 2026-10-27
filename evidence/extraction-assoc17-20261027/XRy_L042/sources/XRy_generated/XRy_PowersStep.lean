import XRy_ArrayMap
open Aeneas Aeneas.Std Result ControlFlow
open XRo_Join_Carriers XRy_LoopWide
set_option autoImplicit false
namespace XRy_PowersStep

theorem mutable {A : Type} {N : Usize} (a : Array A N) (i : Usize) (hi : i.val<N.val) :
 ∃ old, Array.index_mut_usize a i = ok (old,fun x => a.set i x) := by
 obtain ⟨out,hmut,hspec⟩ := WP.spec_imp_exists
   (Array.index_mut_usize_spec a i (by simpa [a.property] using hi))
 rcases out with ⟨old,back⟩
 rcases hspec with ⟨_,hback⟩
 subst back
 exact ⟨old,hmut⟩

theorem step {N : Usize} (x p : C.E) (a : Array C.E N) (i : Usize)
 (hi : i.val<N.val) (hx : XRy_WideMultiply.Canonical x) (hp : XRy_WideMultiply.Canonical p) :
 ∃ i', i'.val=i.val+1 ∧
 ((i'=N ∧
   XRn_Join_Release.weights.powers_loop.body x a p i = ok (.done (a.set i p,some (a.set i p))) ∧
   AspisR1LoopPowers.weights.early_powers_loop.body (toLoop x) (arr toLoop a) (toLoop p) i =
     ok (.done (arr toLoop (a.set i p)))) ∨
  (i'≠N ∧ ∃ p', XRy_WideMultiply.Canonical p' ∧
   XRn_Join_Release.weights.powers_loop.body x a p i = ok (.cont (a.set i p,p',i')) ∧
   AspisR1LoopPowers.weights.early_powers_loop.body (toLoop x) (arr toLoop a) (toLoop p) i =
     ok (.cont (arr toLoop (a.set i p),toLoop p',i')))) := by
 obtain ⟨old,hm⟩ := mutable a i hi
 obtain ⟨old',hm'⟩ := mutable (arr toLoop a) i hi
 have hN : N.val ≤ Usize.max := by scalar_tac
 have hAdd : (i+1#usize : Result Usize) ⦃ j => j.val=i.val+1 ⦄ := by
   apply UScalar.add_spec
   have hone : (1#usize).val=1 := by scalar_tac
   simpa only [hone,UScalar.max_USize_eq] using (show i.val+1 ≤ Usize.max by omega)
 obtain ⟨i',ei,vi⟩ := WP.spec_imp_exists hAdd
 have hlt : i<N := by scalar_tac
 refine ⟨i',vi,?_⟩
 by_cases he : i'=N
 · left
   refine ⟨he,?_,?_⟩
   · simp only [XRn_Join_Release.weights.powers_loop.body,if_pos hlt,hm,ei,bind_tc_ok,he,↓reduceIte]
     rfl
   · simp only [AspisR1LoopPowers.weights.early_powers_loop.body,if_pos hlt,hm',ei,
       bind_tc_ok,he,↓reduceIte,XRy_ArrayMap.set]
     rfl
 · right
   obtain ⟨p',ep,hp',tp⟩ := XRy_LoopWide.multiply p x hp hx
   refine ⟨he,p',hp',?_,?_⟩
   · simp only [XRn_Join_Release.weights.powers_loop.body,if_pos hlt,hm,ei,bind_tc_ok,if_neg he,ep]
     rfl
   · simp only [AspisR1LoopPowers.weights.early_powers_loop.body,if_pos hlt,hm',ei,
       bind_tc_ok,if_neg he,tp,XRy_ArrayMap.set]
     rfl

#print axioms mutable
#print axioms step
end XRy_PowersStep
