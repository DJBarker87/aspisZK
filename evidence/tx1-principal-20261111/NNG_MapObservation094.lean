import NNG_InterpretProjection
set_option autoImplicit false
namespace AspisR1.NNG_MapObservation094
open Aeneas Aeneas.Std Result NMT_CallTree NNG_Observed136 NNG_InterpretProjection
/-- Mapping a child reply preserves every returned/stopped observation and
its exact event prefix; it does not assert a suffix after a stop. -/
theorem mapped {A B C : Type} (decode : A → B) (f : B → C)
 (events : NMT_CallTree.Event → List RSL.Event) (code : Code A) (env : RSL.Env) (m : RSL.Spec B)
 (law : m env (observation decode events code)) :
 RSL.Spec.map f m env (observation (fun a=>f (decode a)) events code) := by
 have same : observation (fun a=>f (decode a)) events code=mapObs f (observation decode events code) := by
  unfold observation
  generalize run code=out
  rcases out with ⟨r,log⟩
  cases r <;> rfl
 rw [same]
 generalize he : observation decode events code=before at law ⊢
 rcases before with ⟨result,ev⟩
 cases result with
 | ret value=>
   exact Or.inl ⟨value,ev,⟨.ret (f value),[]⟩,law,rfl,by simp only [mapObs,mapExit,List.append_nil]⟩
 | abort=>exact Or.inr (Or.inl ⟨ev,law,rfl⟩)
 | diverge=>exact Or.inr (Or.inr ⟨ev,law,rfl⟩)
#print axioms mapped
end AspisR1.NNG_MapObservation094
