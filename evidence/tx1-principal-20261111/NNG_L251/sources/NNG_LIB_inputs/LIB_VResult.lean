import LIB_VRecords
set_option autoImplicit false
namespace LIB_VResult
open Aeneas Aeneas.Std
def value {A B : Type} (f : A→B) (fallback : B) : Result A → B
 | .ok a => f a | .fail _ => fallback | .div => fallback
theorem returns {A B : Type} (f : A→B) (fallback : B)
 (model : RSL.Env→Result A) (events : RSL.Env→List RSL.Event) (env : RSL.Env) :
 NND_Returned.Returns (LIB_Carriers.resultGraph f model events) env (value f fallback (model env)) := by
 intro o b ho hb
 subst o
 cases h : model env with
 | fail e => simp only [LIB_Carriers.resultObs,h] at hb;cases hb
 | div => simp only [LIB_Carriers.resultObs,h] at hb;cases hb
 | ok a =>
  simp only [LIB_Carriers.resultObs,h] at hb
  exact (RSL.Exit.ret.inj hb).symm
theorem functional {A B : Type} (f : A→B) (model : RSL.Env→Result A)
 (events : RSL.Env→List RSL.Event) :
 RSL.Spec.Functional (LIB_Carriers.resultGraph f model events) :=
 fun env => ⟨_,fun _=>Iff.rfl⟩
#print axioms returns
#print axioms functional
end LIB_VResult
