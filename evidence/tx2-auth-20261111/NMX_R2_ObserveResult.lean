import NMX_R2_Carrier
set_option autoImplicit false
namespace NMX_R2_ObserveResult
open Aeneas Aeneas.Std AdapterRw
/-- Projection of an emitted complete Result to the canonical observation.
Only a stopped prefix is returned on fail/div; no post-state is manufactured. -/
def observe {A B : Type} (f : A → B)
 (r : Result (core.result.Result A solana_program_error.ProgramError))
 (events : List RSL.Event := []) : RSL.Obs (Except RSL.ProgramError B) :=
 match r with
 | .ok reply => ⟨.ret (NMX_R2_Carrier.reply f reply),events⟩
 | .fail _ => ⟨.abort,events⟩
 | .div => ⟨.diverge,events⟩

theorem returned_error {A B : Type} (f : A → B) (e : solana_program_error.ProgramError)
 (events : List RSL.Event) :
 observe f (.ok (.Err e)) events = ⟨.ret (.error (NMX_R2_Carrier.error e)),events⟩ := rfl

theorem stopped {A B : Type} (f : A → B) (e : Error) (events : List RSL.Event) :
 observe f (.fail e : Result (core.result.Result A solana_program_error.ProgramError)) events =
 ⟨.abort,events⟩ := rfl
#print axioms returned_error
#print axioms stopped
end NMX_R2_ObserveResult
