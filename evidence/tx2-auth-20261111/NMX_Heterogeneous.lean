import NMX_RawChildren
import NMS_RSLRefine
set_option autoImplicit false
namespace NMX_Heterogeneous
open RSL NMX_RawChildren
/-- Full observation refinement between distinct typed result carriers. -/
def Refines {A B : Type} (encode : A → B) (native : RS A) (model : RS B) : Prop :=
 ∀ env o, native env o → model env (mapObs encode o)

/-- SAME reached reply drives the continuation. Error, abort and divergence
carry the original prefix and do not demand a post-stop value/state. -/
theorem bind {A B C D : Type} (encode : A → B) (output : C → D)
 (native : RS A) (model : RS B) (next : A → RS C) (tail : B → RS D)
 (head : Refines encode native model)
 (suffix : ∀ a, Refines output (next a) (tail (encode a))) :
 Refines output (RS.bind native next) (RS.bind model tail) := by
 intro env observation run
 rcases run with ⟨reply,events,o2,hm,hk,ho⟩ | ⟨events,hm,ho⟩ | ⟨events,hm,ho⟩
 · cases reply with
   | ok a =>
     have child := head env _ hm
     have rest := suffix a env o2 hk
     subst observation
     exact Or.inl ⟨.ok (encode a),events,mapObs output o2,child,rest,by cases o2; rfl⟩
   | error e =>
     have child := head env _ hm
     unfold Spec.pure at hk
     subst o2
     subst observation
     exact Or.inl ⟨.error e,events,⟨.ret (.error e),[]⟩,child,rfl,rfl⟩
 · have child := head env _ hm
   subst observation
   exact Or.inr (Or.inl ⟨events,child,rfl⟩)
 · have child := head env _ hm
   subst observation
   exact Or.inr (Or.inr ⟨events,child,rfl⟩)

#print axioms bind
end NMX_Heterogeneous
