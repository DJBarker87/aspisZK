import NNG_InvokeGraph094
import NNG_DLawStep136
set_option autoImplicit false
namespace AspisR1.NNG_InvokeReturned094
open Aeneas Aeneas.Std Result NMT_CallTree NNG_Observed136

theorem silent {Args A B : Type} (env : RSL.Env) (site : String) (args : Args) (r : Result A)
 (a : A) (decode : A → B) (m : RSL.Spec B)
 (law : m env (observation decode (NNG_Events094.events env) (invoke site args r)))
 (returned : (observation id (NNG_Events094.events env) (invoke site args r)).exit=.ret a)
 (silent : NNG_Events094.events env (.call site args (ok a))=[]) :
 m env ⟨.ret (decode a),[]⟩ := by
 have actual := NNG_DLawStep136.invoke_returned (NNG_Events094.events env) site args r a returned
 have same : observation decode (NNG_Events094.events env) (invoke site args r)=⟨.ret (decode a),[]⟩ := by
  rw [NNG_InvokeGraph094.observation,actual,silent]
  rfl
 exact Eq.mp (congrArg (m env) same) law
#print axioms silent
end AspisR1.NNG_InvokeReturned094
