import NJY_Roots
import NHJ_DeployedIds
set_option autoImplicit false
noncomputable section
namespace NKF_BoxModel
open Aeneas Aeneas.Std Result
abbrev PE := AdapterRw.solana_program_error.ProgramError
/-- Hand transcription of the wrapper tail, after the SAME raw decoder call.
Safe Box::new erases its owned container in the pinned Aeneas model (au).
Native allocation/ownership still requires the (aa) cut, separately recorded. -/
def tail {A F : Type} : core.result.Result A F → core.result.Result A PE
 | .Ok value => .Ok value
 | .Err _ => .Err .InvalidAccountData

def outer {A F : Type} (raw : Result (core.result.Result A F)) :
 Result (core.result.Result A PE) := NJQ_Canonical.mapOuter tail raw

/-- No success premise and no distinguished allocator reservation. This is
only the standard model's value law; it is not an actual allocation proof. -/
def boxValue {A : Type} (_ : AspisR1.NP6_StdModel.Reservation) (value : A) : A := value

theorem box_value {A : Type} (reservation : AspisR1.NP6_StdModel.Reservation) (v : A) :
 boxValue reservation v = v := rfl

theorem error {A F : Type} (e : F) :
 tail (.Err e : core.result.Result A F) = .Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData := rfl

theorem success {A F : Type} (v : A) :
 tail (.Ok v : core.result.Result A F) = .Ok v := rfl

theorem abort {A F : Type} (e : Error) :
 outer (.fail e : Result (core.result.Result A F)) = .fail e := rfl

theorem diverge {A F : Type} :
 outer (.div : Result (core.result.Result A F)) = .div := rfl

/-- The wrapper preserves the entire outer Result and maps every raw error;
no raw error variant is equated to a ProgramError carrier. -/
theorem congruence {A F : Type} (raw : Result (core.result.Result A F))
 (out : core.result.Result A F) (law : ok out = raw) :
 ok (tail out) = outer raw := by
 rw [← law]
 rfl

set_option pp.proofs false in
#print box_value
#print axioms box_value
#print axioms error
#print axioms success
#print axioms abort
#print axioms diverge
#print axioms congruence
end NKF_BoxModel
