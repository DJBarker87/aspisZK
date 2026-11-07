import NMS_R2Refine
set_option autoImplicit false
namespace NMS_R2Success
open RSL
/-- Inversion internal to a returning source path; nonreturning arms cannot
supply a suffix value. -/
theorem bind_return {A B : Type} (first : Spec A) (next : A → Spec B)
 (env : Env) (b : B) (events : List Event)
 (run : Spec.bind first next env ⟨.ret b,events⟩) :
 ∃ a before after, first env ⟨.ret a,before⟩ ∧
  next a env ⟨.ret b,after⟩ ∧ events = before ++ after := by
 rcases run with ⟨a,before,o2,hm,hk,ho⟩ | ⟨_,_,ho⟩ | ⟨_,_,ho⟩
 · cases o2 with
   | mk exit after =>
     cases ho
     exact ⟨a,before,after,hm,hk,rfl⟩
 · cases ho
 · cases ho

theorem pure_return {A : Type} (a b : A) (env : Env) (events : List Event)
 (run : Spec.pure a env ⟨.ret b,events⟩) : b = a :=
 Exit.ret.inj (congrArg Obs.exit run)

#print axioms bind_return
#print axioms pure_return
end NMS_R2Success
