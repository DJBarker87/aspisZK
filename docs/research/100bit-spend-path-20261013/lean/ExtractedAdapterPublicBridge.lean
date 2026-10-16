import ExtractedAdapterCallerBridge
import ExtractedAdapterWithdrawalSuccess
import ExtractedWithdrawalCallerPublic

/-! Reconstruction success and serialization on the fixed request/account/
candidate projection imply the live public parser equation. Authenticated in the
input type's name is not an authentication proof. Stage1 serialization success,
checkpoint binding and a separately supplied public equality stay explicit. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1 AspisR1PublicSerializer
namespace AspisR1AdapterReconstruct.PublicBridge
open aspis_statement.pool_v1.pair_forest_terminal
open aspis_statement.pool_v1.pair_terminal
open r1_pool_adapter

/-- Copy all six snapshot fields and all three candidate fields. -/
def toTransition (a : AuthenticatedAsq8Accounts)
    (candidate : PoolV1PairVerifiedAfterstateV1) : Whole431.Transition :=
  { live_snapshot :=
      { pool := a.live_snapshot.pool
        deployment_domain := a.live_snapshot.deployment_domain
        sequence := a.live_snapshot.sequence
        next_pair_index := a.live_snapshot.next_pair_index
        current_root := a.live_snapshot.current_root
        frontier := a.live_snapshot.frontier }
    candidate_afterstate :=
      { next_pair_index := candidate.next_pair_index
        next_root := candidate.next_root
        next_frontier := candidate.next_frontier } }

def toSerializer (p : CallerBridge.Public) : WithdrawalCarrier431.SerializerPublic :=
  AspisR1WithdrawalCaller.Carrier.toSerializer (CallerBridge.toCaller p)

def projectRaw (p : CallerBridge.Public) (a : AuthenticatedAsq8Accounts)
    (candidate : PoolV1PairVerifiedAfterstateV1) : PublicSourceRaw.Public :=
  AspisR1WithdrawalCaller.CallerPublic.projectRaw (CallerBridge.toCaller p)
    (toTransition a candidate)

/-- The request's exact Withdrawal payload reaches the actual payment encoder.
No nested validator/encoder success is assumed. -/
theorem reconstruct_encoder_success (request : PoolV1PairForestTerminalRequestV1)
    (a : AuthenticatedAsq8Accounts) (candidate : PoolV1PairVerifiedAfterstateV1)
    (out : PoolV1PairForestTerminalStatementV1) (p : CallerBridge.Public)
    (hp : request.«public» = .Withdrawal p)
    (hr : reconstruct_asq8_statement request a candidate = ok (.Ok out)) :
    ∃ pay : Array U8 216#usize,
      AspisR1WithdrawalCaller.pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1
        (CallerBridge.toCaller p) = ok (.Ok pay) := by
  obtain ⟨_, _, hout, hv⟩ := AdapterReconstructSuccess.reconstruct_success
    request a candidate out hr
  have hout' : out = .Withdrawal (AdapterReconstructSuccess.common a candidate) p := by
    simpa only [hp, AdapterReconstructSuccess.statement] using hout
  rw [hout'] at hv
  obtain ⟨pay, he⟩ := WithdrawalSuccess.terminal_encoder_success _ p hv
  exact ⟨pay, CallerBridge.encoder_success p pay he⟩

theorem reconstruct_serializer_parsePublic
    (request : PoolV1PairForestTerminalRequestV1)
    (a : AuthenticatedAsq8Accounts) (candidate : PoolV1PairVerifiedAfterstateV1)
    (out : PoolV1PairForestTerminalStatementV1) (p : CallerBridge.Public)
    (serialized : FieldsRefinement431.ByteVec)
    (hp : request.«public» = .Withdrawal p)
    (hr : reconstruct_asq8_statement request a candidate = ok (.Ok out))
    (hs : AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      (.Withdrawal (toSerializer p) (toTransition a candidate)) = ok (.Ok serialized)) :
    ∃ wire, PublicSourceRaw.toWire (projectRaw p a candidate) = some wire ∧
      SemanticPublicWire.parsePublic (serialized.val.map RawBridge431.rawByte) =
        some (SemanticPublicWire.toPublic wire) := by
  obtain ⟨pay, he⟩ := reconstruct_encoder_success request a candidate out p hp hr
  exact AspisR1WithdrawalCaller.CallerPublic.encoder_serializer_parsePublic
    (CallerBridge.toCaller p) pay (toTransition a candidate) serialized he hs

theorem reconstruct_serializer_supplied_public
    (request : PoolV1PairForestTerminalRequestV1)
    (a : AuthenticatedAsq8Accounts) (candidate : PoolV1PairVerifiedAfterstateV1)
    (out : PoolV1PairForestTerminalStatementV1) (p : CallerBridge.Public)
    (serialized : FieldsRefinement431.ByteVec)
    (hp : request.«public» = .Withdrawal p)
    (hr : reconstruct_asq8_statement request a candidate = ok (.Ok out))
    (hs : AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      (.Withdrawal (toSerializer p) (toTransition a candidate)) = ok (.Ok serialized))
    (wire : SemanticPublicWire.Wire)
    (hw : PublicSourceRaw.toWire (projectRaw p a candidate) = some wire)
    (supplied : R0P.Public SemanticPublicWire.M31)
    (hbind : supplied = SemanticPublicWire.toPublic wire) :
    SemanticPublicWire.parsePublic (serialized.val.map RawBridge431.rawByte) = some supplied := by
  obtain ⟨pay, he⟩ := reconstruct_encoder_success request a candidate out p hp hr
  exact AspisR1WithdrawalCaller.CallerPublic.encoder_serializer_supplied_public
    (CallerBridge.toCaller p) pay (toTransition a candidate) serialized he hs wire hw supplied hbind

#print axioms reconstruct_encoder_success
#print axioms reconstruct_serializer_parsePublic
#print axioms reconstruct_serializer_supplied_public
end AspisR1AdapterReconstruct.PublicBridge
