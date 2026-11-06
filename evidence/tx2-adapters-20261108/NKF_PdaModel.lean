import NKF_BoxModel
set_option autoImplicit false
noncomputable section
namespace NKF_PdaModel
open Aeneas Aeneas.Std Result
abbrev Key := AdapterRw.solana_pubkey.Pubkey
abbrev PdaError := AdapterRw.solana_pubkey.PubkeyError
/-- Value-free op38 relay. This is the parent's map_err continuation, not a
PDA derivation law, SHA computation or SDK ownership/frame certificate. -/
def continuation (reply : Result (core.result.Result Key PdaError)) :=
 NKF_BoxModel.outer reply

theorem success (key : Key) : continuation (ok (.Ok key))=ok (.Ok key) := rfl

theorem error (e : PdaError) : continuation (ok (.Err e))=
 ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData) := rfl

theorem abort (e : Error) : continuation (.fail e)=.fail e := rfl

theorem divergence : continuation .div=.div := rfl

/-- No later continuation runs after the first failing/aborting operation. -/
theorem no_suffix {A B : Type} (e : Error) (next : A → Result B) :
 (do let a ← (Result.fail e : Result A); next a)=Result.fail e := rfl

set_option pp.proofs false in
#print success
#print axioms success
#print axioms error
#print axioms abort
#print axioms divergence
#print axioms no_suffix
end NKF_PdaModel
