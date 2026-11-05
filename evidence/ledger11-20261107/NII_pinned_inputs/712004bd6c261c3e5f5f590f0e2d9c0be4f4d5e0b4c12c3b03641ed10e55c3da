import NGL_CloneDomain
import NGL_ReadonlyModel
import NGL_CheckpointModel
set_option autoImplicit false
noncomputable section
namespace NGL_HelperFrames
open Aeneas Aeneas.Std Result
abbrev A := NGL_CloneDomain.Account
abbrev PE := AdapterRw.solana_program_error.ProgramError
abbrev K := AdapterRw.solana_pubkey.Pubkey

def attach {X State : Type} (r : Result X) (a : A) (state : State) :
    Result X × A × State × List Unit := (r,a,state,[])

/-- Value is the actual emitted body. The identity state/effects projection is
    the frame paired with the separate native empty-modifies certificate. -/
theorem length {State : Type} (ops : AdapterRw.Ops) (a : A) (state : State) :
    attach (AdapterRw.r1_pool_adapter.owned.OwnedAccount.data_len (NGL_CloneDomain.install ops) a) a state =
      (ok a.length,a,state,[]) := by
  rw [NGL_CloneDomain.length_result]
  rfl

theorem data {State : Type} (ops : AdapterRw.Ops) (a : A) (state : State) :
    attach (AdapterRw.r1_pool_adapter.owned.OwnedAccount.data (NGL_CloneDomain.install ops) a) a state =
      (ok (match a.bytes with | .Ok v => .Ok v.deref | .Err e => .Err e),a,state,[]) := by
  rw [NGL_CloneDomain.data_result]
  rfl

theorem checkpoint {State : Type} (ops : AdapterRw.Ops) (a : A) (program : K)
    (writable : Bool) (state : State) :
    attach (AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint
      (NGL_CheckpointModel.install ops) a program writable) a state =
      (ok (NGL_CheckpointModel.reply a program writable),a,state,[]) := by
  rw [NGL_CheckpointModel.result]
  rfl

#print axioms length
#print axioms data
#print axioms checkpoint
end NGL_HelperFrames
