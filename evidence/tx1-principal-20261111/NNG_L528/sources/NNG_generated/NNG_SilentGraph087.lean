import NNG_Events087
import NNG_FinishOccurrence137
import NNG_ConcreteGraph136
set_option autoImplicit false
namespace AspisR1.NNG_SilentGraph087
open Aeneas Aeneas.Std Result NMT_CallTree NNG_Observed136

theorem observation {Args A B : Type} (env : RSL.Env) (site : String) (args : Args)
 (r : Result A) (decode : A → B) (value : B)
 (projected : NNG_EmittedCallGraph.resultMap decode r=.ok value)
 (silent : NNG_Events087.events env (.call site args r)=[]) :
 NNG_Observed136.observation decode (NNG_Events087.events env) (invoke site args r)=⟨.ret value,[]⟩ := by
 unfold NNG_Observed136.observation
 rw [NNG_FinishOccurrence137.run_invoke]
 simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,silent]
 exact NNG_ConcreteGraph136.resultObs decode r (.ok value) [] projected
#print axioms observation
end AspisR1.NNG_SilentGraph087
