import NMX_ObserveResult
import NMX_RawChildren
set_option autoImplicit false
namespace NMX_ResultRelation
open Aeneas Aeneas.Std AdapterRw NMX_Carrier NMX_RawChildren

def rust {A : Type} (r : Result (core.result.Result A solana_program_error.ProgramError)) : RSL.RS A :=
 fun _ o => o = NMX_ObserveResult.observe id r

def rawObs {A : Type} : Result A → RSL.Obs (Except RSL.ProgramError A)
 | .ok a => ⟨.ret (.ok a),[]⟩
 | .fail _ => ⟨.abort,[]⟩
 | .div => ⟨.diverge,[]⟩

def raw {A : Type} (r : Result A) : RSL.RS A := fun _ o => o = rawObs r

theorem map_rust {A B : Type} (encode : A → B)
 (r : Result (core.result.Result A solana_program_error.ProgramError)) :
 mapObs encode (NMX_ObserveResult.observe id r) = NMX_ObserveResult.observe encode r := by
 cases r with
 | fail e => rfl
 | div => rfl
 | ok reply => cases reply <;> rfl
#print axioms map_rust
end NMX_ResultRelation
