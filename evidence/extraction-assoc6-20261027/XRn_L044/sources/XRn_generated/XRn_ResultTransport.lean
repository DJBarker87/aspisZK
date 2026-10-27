import XRn_Carriers
open Aeneas Aeneas.Std Result ControlFlow
open XRn_Carriers
set_option autoImplicit false
namespace XRn_ResultTransport

theorem map_ok {A B : Type} (f : A → B) (a : A) : mapR f (ok a)=ok (f a) := rfl
theorem map_fail {A B : Type} (f : A → B) (e : Aeneas.Std.Error) : mapR f (.fail e)=.fail e := rfl
theorem map_div {A B : Type} (f : A → B) : mapR f (.div : Result A)=.div := rfl

theorem map_if {A B : Type} (f : A → B) (p : Prop) [Decidable p] (x y : Result A) :
 mapR f (if p then x else y)=if p then mapR f x else mapR f y := by split <;> rfl

theorem map_pair {A B F G : Type} (f : F → G) (p : A × B) (k : A → B → Result F) :
 mapR f (match p with | (a,b)=>k a b)=match p with | (a,b)=>mapR f (k a b) := by cases p; rfl

theorem map_flow {A B F G : Type} (f : F → G) (p : core.ops.control_flow.ControlFlow A B)
 (k : B → Result F) (h : A → Result F) :
 mapR f (match p with | .Continue b=>k b | .Break a=>h a)=
 match p with | .Continue b=>mapR f (k b) | .Break a=>mapR f (h a) := by cases p <;> rfl

theorem map_inner {A B F G : Type} (f : F → G) (p : core.result.Result A B)
 (k : A → Result F) (h : B → Result F) :
 mapR f (match p with | .Ok a=>k a | .Err b=>h b)=
 match p with | .Ok a=>mapR f (k a) | .Err b=>mapR f (h b) := by cases p <;> rfl

theorem map_comp {A B F : Type} (f : A → B) (g : B → F) (r : Result A) :
 mapR g (mapR f r)=mapR (g ∘ f) r := by cases r <;> rfl

theorem bind_map {A B F : Type} (f : A → B) (r : Result A) (k : B → Result F) :
 (mapR f r >>= k)=r >>= (fun a=>k (f a)) := by cases r <;> rfl

theorem map_id {A : Type} (r : Result A) : mapR id r=r := by cases r <;> rfl

theorem map_injective {A B : Type} (f : A → B) (hf : Function.Injective f)
 (r s : Result A) (h : mapR f r=mapR f s) : r=s := by
 cases r <;> cases s <;> simp only [mapR,bind_tc_ok,bind_tc_fail,bind_tc_div] at h ⊢
 all_goals first | cases h | rfl | exact congrArg Result.ok (hf (Result.ok.inj h))

#print axioms map_ok
#print axioms map_fail
#print axioms map_div
#print axioms map_if
#print axioms map_pair
#print axioms map_flow
#print axioms map_inner
#print axioms map_comp
#print axioms bind_map
#print axioms map_id
#print axioms map_injective
end XRn_ResultTransport
