import PCM_Witness
import PCM_ErrorLaws
set_option autoImplicit false
namespace PCM
open RSL Computation

theorem rejects_avoided_error {A B : Type} (domain : A → Prop)
    (ref : A → Computation B) (a : A) (ha : domain a) (bad : ProgramError)
    (avoid : Avoid bad (ref a)) :
    ¬ PCM.RowSpec domain ref (fun _ s _ => ⟨.ret (.error bad,s),[]⟩) := by
  intro h
  exact avoid PCM.state0 env0 PCM.state0 [] (h a ha PCM.state0 env0)
#print axioms rejects_avoided_error
end PCM
