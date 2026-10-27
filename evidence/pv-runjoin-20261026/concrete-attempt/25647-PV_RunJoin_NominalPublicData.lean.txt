import R1Z.PV_RunJoin_NominalCompiledData
import R1Z.PV_Src_NativeInput
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NominalPublicData
open PV_RunJoin_NominalCompiledData

abbrev TargetTransfer := PDict_StatementTypes.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1
abbrev TargetWithdrawal := PDict_StatementTypes.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1
abbrev TargetPublic (base : ProverRwFull.ExternalTypes) :=
  @ProverRwFull.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public (PDict_CodecDictionary.native base)

def transfer (p : BuilderPublicProjection.Transfer) : TargetTransfer where
  pool := p.pool
  deployment_domain := p.deployment_domain
  anchor_sequence := p.anchor_sequence
  anchor_root := p.anchor_root
  nullifier := p.nullifier
  asset_id := p.asset_id
  recipient_commitment := p.recipient_commitment
  change_commitment := p.change_commitment

def withdrawal (p : BuilderPublicProjection.Withdrawal) : TargetWithdrawal where
  pool := p.pool
  deployment_domain := p.deployment_domain
  anchor_sequence := p.anchor_sequence
  anchor_root := p.anchor_root
  nullifier := p.nullifier
  asset_id := p.asset_id
  amount := p.amount
  destination_token_account := p.destination_token_account
  change_commitment := p.change_commitment

def publicTransition (base : ProverRwFull.ExternalTypes) (t : BuilderPublicProjection.Transition) :
    TargetTransition base := by
  letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
  exact {
    live_snapshot := {
      pool := t.live_snapshot.pool
      deployment_domain := t.live_snapshot.deployment_domain
      sequence := t.live_snapshot.sequence
      next_pair_index := t.live_snapshot.next_pair_index
      current_root := t.live_snapshot.current_root
      frontier := t.live_snapshot.frontier }
    candidate_afterstate := {
      next_pair_index := t.candidate_afterstate.next_pair_index
      next_root := t.candidate_afterstate.next_root
      next_frontier := t.candidate_afterstate.next_frontier } }

def fromPublicInput (base : ProverRwFull.ExternalTypes) (p : PV_Src_Public.Input) : TargetPublic base :=
  letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
  match p with
  | .transfer pub transition => .Transfer (transfer pub) (publicTransition base transition)
  | .withdrawal pub transition => .Withdrawal (withdrawal pub) (publicTransition base transition)

/-- The full client public value uses the same request and public statement
as the selected actual compiler record. No scalar field is dropped. -/
def fromInput (base : ProverRwFull.ExternalTypes) (i : PV_Src_NativeInput.Input) : TargetPublic base :=
  letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
  match i.request with
  | .transfer pub _ => .Transfer (transfer pub) (transition base i.compiled.public_statement)
  | .withdrawal pub => .Withdrawal (withdrawal pub) (transition base i.compiled.public_statement)

theorem selected_public (base : ProverRwFull.ExternalTypes) (i : PV_Src_NativeInput.Input) :
    fromInput base i = fromPublicInput base (PV_Src_NativeInput.publicInput i) := by
  cases i with
  | mk request witness change lane snapshot compiled => cases request <;> rfl

#print axioms selected_public
end R1Z.PV_RunJoin_NominalPublicData
