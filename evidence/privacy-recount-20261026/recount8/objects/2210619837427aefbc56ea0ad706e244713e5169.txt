import R1Z.PV_RunJoin_EnteredCaller
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PublicDecision
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
open PV_RunJoin_LedgerWorld
variable [ExternalTypes]

def decision (ops : ExternalFuns) (address : Address) (pub : Pub)
    (variant : transport.Variant) (hash : Hash) (nonce : Array U8 32#usize) :
    Option ProverCommitLedger36.Path :=
  letI : ExternalFuns := ops
  match PV_RunJoin_PublicReservation.entry address pub variant hash nonce with
  | .ok path => path
  | .fail _ | .div => none

theorem returned (ops : ExternalFuns) (schedule : ProverCommitLedger36.Schedule)
    (unix : Bool) (address : Address) (pub : Pub) (compiled : Compiled)
    (variant : transport.Variant) (secret : Secret) (hash : Hash) (s after : World)
    (status : core.result.Result Proof verifier.Error) (empty : s.entered = none)
    (run : letI : ExternalFuns := ops
      PV_RunJoin_GenericSourceCaller.caller (dictionary ops schedule unix address)
        pub compiled variant hash secret s = .ok (status,after)) :
    decision ops address pub variant hash secret.mask_nonce = after.entered := by
  letI : ExternalFuns := ops
  have entered := PV_RunJoin_EnteredCaller.caller ops schedule unix address pub compiled
    variant secret hash s empty (status,after) run
  unfold decision
  rw [entered]

/-- The common function uses no compiled columns. This equality preserves
all source-prefix errors and divergence through the definition of decision. -/
theorem common (ops : ExternalFuns) (address : Address) (pub pub' : Pub)
    (variant : transport.Variant) (hash hash' : Hash) (nonce nonce' : Array U8 32#usize)
    (same_public : pub = pub') (same_hash : hash = hash') (same_nonce : nonce = nonce') :
    decision ops address pub variant hash nonce = decision ops address pub' variant hash' nonce' := by
  rw [same_public,same_hash,same_nonce]

#print axioms returned
#print axioms common
end R1Z.PV_RunJoin_PublicDecision
