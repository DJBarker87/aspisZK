import NNG_Events094
import NNG_ObservationAlgebra
set_option autoImplicit false
namespace AspisR1.NNG_Silent094
open Aeneas Aeneas.Std Result NMT_CallTree NNG_Observed136
/-- The actual None-observer marks retain no visible event and preserve
both the value and the exact continuation. -/
theorem invoke_ok {A B C Args : Type} (decode : B → C) (env : RSL.Env) (site : String)
 (args : Args) (value : A) (k : A → Code B)
 (silent : NNG_Events094.events env (.call site args (.ok value))=[]) :
 observation decode (NNG_Events094.events env) (NMT_CallTree.bind (invoke site args (.ok value)) k)=
 observation decode (NNG_Events094.events env) (k value) := by
 rw [NNG_ObservationAlgebra.observation_bind]
 simp only [observation,invoke,run,List.flatMap_cons,List.flatMap_nil,List.append_nil,exit,id_eq]
 rw [silent]
 simp only [NNG_ObservationAlgebra.append,List.nil_append]
#print axioms invoke_ok
end AspisR1.NNG_Silent094
