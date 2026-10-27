import XSa_ArrayPrefix
open Aeneas Aeneas.Std Result ControlFlow
open XRo_Join_Carriers
set_option autoImplicit false
namespace XSa_PowersStep

theorem last {N : Usize} (x p : C.E) (a : Array C.E N) (i : Usize)
 (hx : XRy_WideMultiply.Canonical x) (hp : XRy_WideMultiply.Canonical p)
 (hi : i.val+1=N.val) :
 XRn_Join_Release.weights.powers_loop.body x a p i=ok (.done (a.set i p,some (a.set i p))) := by
 obtain ⟨j,hj,hcases⟩ := XRy_PowersStep.step x p a i (by omega) hx hp
 rcases hcases with ⟨he,hr,ht⟩ | ⟨he,rest⟩
 · exact hr
 · have heq : j=N := UScalar.eq_of_val_eq (by omega)
   exact False.elim (he heq)

theorem next {N : Usize} (x p : C.E) (a : Array C.E N) (i : Usize)
 (hx : XRy_WideMultiply.Canonical x) (hp : XRy_WideMultiply.Canonical p)
 (hi : i.val+1<N.val) :
 ∃ j p', j.val=i.val+1 ∧ XRy_WideMultiply.Canonical p' ∧
 _root_.aspis_core.field.wide_exact.WideExact.mul p x=ok p' ∧
 XRn_Join_Release.weights.powers_loop.body x a p i=ok (.cont (a.set i p,p',j)) := by
 obtain ⟨old,hm⟩ := XRy_PowersStep.mutable a i (by omega)
 obtain ⟨j,ej,hj⟩ := WP.spec_imp_exists
   (UScalar.add_spec (x:=i) (y:=1#usize) (by have hN : N.val≤Usize.max := by scalar_tac; scalar_tac))
 obtain ⟨p',em,hp',ht⟩ := XRy_LoopWide.multiply p x hp hx
 have hlt : i<N := by scalar_tac
 have he : j≠N := by intro h; subst j; scalar_tac
 refine ⟨j,p',by scalar_tac,hp',em,?_⟩
 simp only [XRn_Join_Release.weights.powers_loop.body,if_pos hlt,hm,ej,bind_tc_ok,he,if_false,em]
 rfl

#print axioms last
#print axioms next
end XSa_PowersStep
