import NNG_FinishOccurrence137
import LIB_Carriers
set_option autoImplicit false
namespace AspisR1.NNG_InvokeGraph328
open Aeneas Aeneas.Std Result NMT_CallTree NNG_Observed136
/-- Generic structural prefix rule; no accuracy of an arbitrary event decoder
is claimed. Each actual caller supplies its own checked typed interpretation. -/
theorem observation {A B Args : Type} (decode : A → B) (events : NMT_CallTree.Event → List RSL.Event)
 (site : String) (args : Args) (r : Result A) :
 NNG_Observed136.observation decode events (invoke site args r)=
 LIB_Carriers.resultObs decode (events (.call site args r)) r := by
 unfold NNG_Observed136.observation
 rw [NNG_FinishOccurrence137.run_invoke]
 simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
 cases r <;> rfl
#print axioms observation
end AspisR1.NNG_InvokeGraph328
