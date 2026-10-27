import R1Z.PV_RunJoin_EnteredBody
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_EnteredCaller
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
open PV_RunJoin_Follows PV_RunJoin_LedgerWorld
variable [ExternalTypes]

theorem caller (ops : ExternalFuns) (schedule : ProverCommitLedger36.Schedule)
    (unix : Bool) (address : Address) (pub : Pub) (compiled : Compiled)
    (variant : transport.Variant) (secret : Secret) (hash : Hash) (s : World)
    (empty : s.entered = none) :
    letI : ExternalFuns := ops
    Follows (fun out : core.result.Result Proof verifier.Error × World => out.2.entered)
      (PV_RunJoin_PublicReservation.entry address pub variant hash secret.mask_nonce)
      (PV_RunJoin_GenericSourceCaller.caller (dictionary ops schedule unix address)
        pub compiled variant hash secret s) := by
  letI : ExternalFuns := ops
  unfold PV_RunJoin_PublicReservation.entry PV_RunJoin_GenericSourceCaller.caller
  apply bind_common
  intro publicBytes
  apply bind_common
  intro mapped
  apply bind_common
  intro branch
  cases branch with
  | Continue bytes =>
    apply bind_common
    intro prepared
    rcases prepared with ⟨context,binding⟩
    exact PV_RunJoin_EnteredBody.body ops schedule unix address pub compiled variant secret hash binding context s empty
  | Break residual =>
    apply bind_common
    intro error
    simpa only [empty] using returned
      (fun out : core.result.Result Proof verifier.Error × World => out.2.entered) (error,s)

#print axioms caller
end R1Z.PV_RunJoin_EnteredCaller
