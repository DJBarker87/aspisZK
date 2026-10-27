import R1Z.PV_RunJoin_CallerProjection
import R1Z.PV_RunJoin_LedgerWorld
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LedgerSourceProjection
open Aeneas Aeneas.Std Result ProverRwFull ProverRwRetryModel
open ProverCommitSemanticTransport26 PV_RunJoin_LedgerWorld
variable [ExternalTypes]

/-- Full emitted caller/header projection. Native outcomes and history are
retained by the world; their E1/E2 laws are separate obligations. -/
theorem caller (ops : ExternalFuns) (identity : PV_RunJoin_MapErrInstalled.Identity ops)
    (schedule : ProverCommitLedger36.Schedule) (unix : Bool) (address : Address)
    (pub : Pub) (compiled : Compiled) (variant : transport.Variant) (hash : Hash)
    (secret : Secret) (s : World) :
    letI : ExternalFuns := ops
    mapR (fun out => (out.1,out.2.header))
      (PV_RunJoin_GenericSourceCaller.caller (dictionary ops schedule unix address)
        pub compiled variant hash secret s) =
    prover.prove_masked_attempt pub compiled variant hash secret s.header := by
  letI : ExternalFuns := ops
  rw [← PV_RunJoin_GenericSourceCaller.source_eq]
  exact PV_RunJoin_CallerProjection.caller (PV_RunJoin_MapErrInstalled.installed ops identity)
    (fun world : World => world.header) (dictionary ops schedule unix address) _
    pub compiled variant hash secret s
    (fun statement nonce => source_projection ops schedule unix address s statement nonce)

#print axioms caller
end R1Z.PV_RunJoin_LedgerSourceProjection
