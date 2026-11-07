import LIBB_ResultTotal
import NMS_R2N_Regular
import NND_Returned
set_option autoImplicit false
namespace LIBB_ModelGraph
open Aeneas Aeneas.Std
/-- Evaluator for returned values. On a stopped model no return is asserted. -/
def value {A : Type} (fallback : A) : Result A → A
 | .ok x => x | .fail _ => fallback | .div => fallback
/-- This premise is instantiated by a CLOSED model's own regularity theorem,
never exported as a candidate/root assumption. -/
theorem returned {A : Type} (m : RSL.Spec A) (code : Result A) (fallback : A)
 (law : NMS_R2N_Regular.Law m code) (env : RSL.Env) :
 NND_Returned.Returns m env (value fallback code) := by
 intro o r h hr
 cases o with
 | mk exit events =>
   change exit = .ret r at hr
   subst exit
   have same := law env r events h
   rw [same]
   rfl

theorem lift_returned {A : Type} (code : Result A) (fallback : A) (env : RSL.Env) :
 NND_Returned.Returns (NMS_R2N_Interpreted.liftResult code) env (value fallback code) :=
 returned _ code fallback (NMS_R2N_Regular.lift code) env

/-- The ordinary Result interpretation is exactly its observation graph. -/
theorem lift_graph {A : Type} (code : Result A) (env : RSL.Env) (o : RSL.Obs A) :
 NMS_R2N_Interpreted.liftResult code env o ↔
 o = LIB_Carriers.resultObs id [] code := by
 cases code <;> rfl

/-- Representation mapping preserves stops and the complete ordered prefix. -/
theorem mapped_member {A B : Type} (f : A → B) (m : RSL.Spec A) :
 NMS_R2N_Interpreted.Simulates f m (RSL.Spec.map f m) := by
 intro env o h
 cases o with
 | mk exit events =>
   cases exit with
   | ret a =>
     exact Or.inl ⟨a,events,⟨.ret (f a),[]⟩,h,rfl,by simp [NMS_R2N_Interpreted.mapObs,NMS_R2N_Interpreted.mapExit]⟩
   | abort => exact Or.inr (Or.inl ⟨events,h,rfl⟩)
   | diverge => exact Or.inr (Or.inr ⟨events,h,rfl⟩)
#print axioms returned
#print axioms lift_returned
#print axioms lift_graph
#print axioms mapped_member
end LIBB_ModelGraph
