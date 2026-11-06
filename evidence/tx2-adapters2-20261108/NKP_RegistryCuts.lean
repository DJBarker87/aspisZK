import NKF_PdaModel
set_option autoImplicit false
noncomputable section
namespace NKP_RegistryCuts
open Aeneas Aeneas.Std Result
abbrev PE := NKF_BoxModel.PE
abbrev Reply := core.result.Result Unit PE
/-- Local comparison-stage result, not a root runtime assumption. `reject`
is the Boolean OR of the exact frozen guard in each NKP_K070..K079_CUT.json.
A parent must compute it from the SAME decoded records, keys and current_slot.
This module does not supply the missing data/decoder/PDA invocation chain. -/
def result (reject : Bool) : Reply :=
 if reject then .Err .InvalidAccountData else .Ok ()

/-- Transcription of `if expected {matches!(result,Ok(()))} else
{matches!(result,Err(InvalidAccountData))}`, expected = !reject. Every stage
has empty external modifies; only its local Result changes. Exact frozen
segments/hashes and matched controls are in the per-attempt CUT receipts. -/
def Cut (reject : Bool) (out : Reply) : Prop :=
 match reject with
 | true => out = .Err .InvalidAccountData
 | false => out = .Ok ()

theorem comparison (reject : Bool) (out : Reply) (cut : Cut reject out) :
 out = result reject := by
 cases reject <;> exact cut

/-- The source `return Err` in a comparison stage never enters its suffix.
This is the local frame chain only, not authentication of either registry. -/
def advance (out : Reply) (next : Unit → Reply) : Reply :=
 match out with
 | .Err e => .Err e
 | .Ok u => next u

theorem rejection_no_suffix (out : Reply) (next : Unit → Reply)
 (cut : Cut true out) : advance out next = .Err .InvalidAccountData := by
 rw [comparison true out cut]
 rfl

theorem accepted_continuation (out : Reply) (next : Unit → Reply)
 (cut : Cut false out) : advance out next = next () := by
 rw [comparison false out cut]
 rfl

#print axioms comparison
#print axioms rejection_no_suffix
#print axioms accepted_continuation
end NKP_RegistryCuts
