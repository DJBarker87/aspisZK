import NDM_AdoptedReconstruction
import NDM_GateTotal
import NEC_Common
set_option autoImplicit false
namespace NEC_Reconstruction
open Aeneas Aeneas.Std Result AdapterRw
open AspisR1.JHf_Carrier
abbrev Request := aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
abbrev Auth := r1_pool_adapter.AuthenticatedAsq8Accounts
abbrev Candidate := NDM_CommonCarrier.Candidate

def PacketDomain (_request : Request) (_a : Auth) (_c : Candidate) : Prop := True

theorem caller_domain (request : Request) (a : Auth) (c : Candidate) : PacketDomain request a c := True.intro

theorem common_domain (a : Auth) (c : Candidate) : NEC_Common.PacketDomain a c := NEC_Common.caller_domain a c

/-- Existing coherent op52 selection; no replacement dictionary or stand-in. -/
theorem selected (request : Request) (a : Auth) (c : Candidate) :
 AspisR1.JHf_ReconstructionSlot.source request a c =
 (do let raw ← NDM_CohortReconstruction.direct (toRequest request)
       (toAuthenticatedAsq8Accounts a) (toPoolV1PairVerifiedAfterstateV1 c)
     ok (NDM_CohortStatement.transport raw)) := NDM_AdoptedReconstruction.selected request a c

/-- Safe Rust checked-add reference already extracted with the NCO pins. -/
theorem gate (live next : U64) :
 NDM_GateRef.next_gate_ref live next=ok (decide (live.val+1=next.val)) :=
 NDM_GateTotal.reference live next

#print axioms caller_domain
#print axioms common_domain
#print axioms selected
#print axioms gate
end NEC_Reconstruction
