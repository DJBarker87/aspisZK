import NNG_Events094
import NNG_FinishOccurrence137
set_option autoImplicit false
namespace AspisR1.NNG_InvokeGraph094
open Aeneas Aeneas.Std Result NMT_CallTree NNG_Observed136
/-- Exact effect prefix of one typed emitted occurrence, including stopping
arms. This exposes only the SAME call's source-defined event interpretation. -/
theorem observation {A B Args : Type} (decode : A → B) (env : RSL.Env)
 (site : String) (args : Args) (r : Result A) :
 NNG_Observed136.observation decode (NNG_Events094.events env) (invoke site args r)=
 LIB_Carriers.resultObs decode (NNG_Events094.events env (.call site args r)) r := by
 unfold NNG_Observed136.observation
 rw [NNG_FinishOccurrence137.run_invoke]
 simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
 cases r <;> rfl
#print axioms observation
end AspisR1.NNG_InvokeGraph094
