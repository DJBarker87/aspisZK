import LIB_Carriers
set_option autoImplicit false
namespace LIBC_ResultGraph
open Aeneas Aeneas.Std
/-- Fallback only chooses a total evaluator on stopped arms; it never creates
a returned observation, post-abort value, or post-abort state. -/
def value {A B : Type} (f : A → B) (fallback : B) : Result A → B
 | .ok a => f a | .fail _ => fallback | .div => fallback
theorem returns {A B : Type} (f : A → B) (fallback : B)
 (model : RSL.Env → Result A) (events : RSL.Env → List RSL.Event) (env : RSL.Env) :
 NND_Returned.Returns (LIB_Carriers.resultGraph f model events) env (value f fallback (model env)) := by
 intro o r ho hr
 subst o
 cases h : model env with
 | ok a =>
  simp only [h,LIB_Carriers.resultObs] at hr
  simpa only [value,h] using (RSL.Exit.ret.inj hr).symm
 | fail e => simp only [h,LIB_Carriers.resultObs] at hr;cases hr
 | div => simp only [h,LIB_Carriers.resultObs] at hr;cases hr
theorem functional {A B : Type} (f : A → B) (model : RSL.Env → Result A)
 (events : RSL.Env → List RSL.Event) :
 RSL.Spec.Functional (LIB_Carriers.resultGraph f model events) := by
 intro env
 exact ⟨LIB_Carriers.resultObs f (events env) (model env),fun _ => Iff.rfl⟩
#print axioms returns
#print axioms functional
end LIBC_ResultGraph
