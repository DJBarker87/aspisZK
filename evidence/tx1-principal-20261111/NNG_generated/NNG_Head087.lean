import NNG_ObservationAlgebra
import NNG_Events087
set_option autoImplicit false
namespace AspisR1.NNG_Head087
open Aeneas Aeneas.Std Result NMT_CallTree NNG_Observed136

theorem invoke_ok {A B C Args : Type} (decode : B → C) (env : RSL.Env) (site : String)
 (args : Args) (value : A) (k : A → Code B)
 (silent : NNG_Events087.events env (.call site args (.ok value))=[]) :
 observation decode (NNG_Events087.events env) (NMT_CallTree.bind (invoke site args (.ok value)) k)=
 observation decode (NNG_Events087.events env) (k value) := by
 rw [NNG_ObservationAlgebra.observation_bind]
 simp only [observation,invoke,run,List.flatMap_cons,List.flatMap_nil,List.append_nil,exit,id_eq]
 rw [silent]
 simp only [NNG_ObservationAlgebra.append,List.nil_append]

theorem plain_ok {A B C : Type} (decode : B → C) (events : Event → List RSL.Event)
 (value : A) (k : A → Code B) :
 observation decode events (NMT_CallTree.bind (Code.plain (.ok value) .done) k)=
 observation decode events (k value) := rfl
#print axioms invoke_ok
#print axioms plain_ok
end AspisR1.NNG_Head087
