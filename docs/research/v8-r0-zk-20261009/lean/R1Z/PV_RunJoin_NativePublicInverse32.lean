import R1Z.PV_RunJoin_NominalPublicData
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NativePublicInverse32
open PV_RunJoin_NominalPublicData

def unTransfer (p : TargetTransfer) : BuilderPublicProjection.Transfer where
  pool := p.pool
  deployment_domain := p.deployment_domain
  anchor_sequence := p.anchor_sequence
  anchor_root := p.anchor_root
  nullifier := p.nullifier
  asset_id := p.asset_id
  recipient_commitment := p.recipient_commitment
  change_commitment := p.change_commitment

def unWithdrawal (p : TargetWithdrawal) : BuilderPublicProjection.Withdrawal where
  pool := p.pool
  deployment_domain := p.deployment_domain
  anchor_sequence := p.anchor_sequence
  anchor_root := p.anchor_root
  nullifier := p.nullifier
  asset_id := p.asset_id
  amount := p.amount
  destination_token_account := p.destination_token_account
  change_commitment := p.change_commitment

theorem transfer_roundtrip (p : BuilderPublicProjection.Transfer) :
    unTransfer (transfer p) = p := by cases p; rfl
#print axioms transfer_roundtrip

theorem withdrawal_roundtrip (p : BuilderPublicProjection.Withdrawal) :
    unWithdrawal (withdrawal p) = p := by cases p; rfl
#print axioms withdrawal_roundtrip

theorem target_transfer_roundtrip (p : TargetTransfer) :
    transfer (unTransfer p) = p := by cases p; rfl
#print axioms target_transfer_roundtrip

theorem target_withdrawal_roundtrip (p : TargetWithdrawal) :
    withdrawal (unWithdrawal p) = p := by cases p; rfl
#print axioms target_withdrawal_roundtrip

def unPublicTransition (base : ProverRwFull.ExternalTypes)
    (t : PV_RunJoin_NominalCompiledData.TargetTransition base) :
    BuilderPublicProjection.Transition := by
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

def unPublic (base : ProverRwFull.ExternalTypes) (p : TargetPublic base) : PV_Src_Public.Input := by
  letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
  exact match p with
    | .Transfer pub transition => .transfer (unTransfer pub)
        (unPublicTransition base transition)
    | .Withdrawal pub transition => .withdrawal (unWithdrawal pub)
        (unPublicTransition base transition)

theorem from_public_roundtrip (base : ProverRwFull.ExternalTypes) (p : PV_Src_Public.Input) :
    unPublic base (fromPublicInput base p) = p := by
  cases p <;> rfl
#print axioms from_public_roundtrip

theorem from_input_roundtrip (base : ProverRwFull.ExternalTypes) (i : PV_Src_NativeInput.Input) :
    unPublic base (fromInput base i) = PV_Src_NativeInput.publicInput i := by
  rw [selected_public,from_public_roundtrip]
#print axioms from_input_roundtrip

theorem target_transition_roundtrip (base : ProverRwFull.ExternalTypes)
    (t : PV_RunJoin_NominalCompiledData.TargetTransition base) :
    publicTransition base (unPublicTransition base t) = t := by
  letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
  cases t
  rfl
#print axioms target_transition_roundtrip

theorem to_public_roundtrip (base : ProverRwFull.ExternalTypes) (p : TargetPublic base) :
    fromPublicInput base (unPublic base p) = p := by
  letI : ProverRwFull.ExternalTypes := PDict_CodecDictionary.native base
  cases p <;> rfl
#print axioms to_public_roundtrip

/-- A complete source public input survives nominal translation. In particular,
pool/deployment, anchor sequence, withdrawal destination and transition fields
are retained even where a later semantic projection omits them. -/
theorem injective (base : ProverRwFull.ExternalTypes) :
    Function.Injective (fromPublicInput base) := by
  intro p q h
  have same := congrArg (unPublic base) h
  simpa only [from_public_roundtrip] using same
#print axioms injective
end R1Z.PV_RunJoin_NativePublicInverse32
