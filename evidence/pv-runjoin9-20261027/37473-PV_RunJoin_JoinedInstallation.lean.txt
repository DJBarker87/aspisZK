import R1Z.PV_Join_FixtureInputs
import R1Z.PV_RunJoin_MapErrInstalled
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_JoinedInstallation
open Aeneas Aeneas.Std Result ProverRwFull
variable [ProverRwRngCaller.NativeTypes] [ProverRwRngCaller.ErasureFns]

/-- op12 belongs to the actual joined caller selector, including P8. -/
theorem identity (base : ExternalTypes)
    (ops : @ExternalFuns (PV_Join_PublicCaller.native base)) :
    @PV_RunJoin_MapErrInstalled.Identity (PV_Join_PublicCaller.native base)
      (PV_Join_PublicCaller.selected base ops) := rfl

def transition (base : ExternalTypes) (t : BuilderPublicProjection.Transition) :
    @aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1
      (PV_Join_PublicCaller.native base) := by
  letI : ExternalTypes := PV_Join_PublicCaller.native base
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

def publicInput (base : ExternalTypes) (p : PV_Src_Public.Input) :
    @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
      (PV_Join_PublicCaller.native base) := by
  letI : ExternalTypes := PV_Join_PublicCaller.native base
  exact match p with
    | .transfer pub t => .Transfer (PV_RunJoin_NominalPublicData.transfer pub) (transition base t)
    | .withdrawal pub t => .Withdrawal (PV_RunJoin_NominalPublicData.withdrawal pub) (transition base t)

/-- Convert the selected record's public projection at the joined carrier,
without identifying its ExternalTypes dictionary with the codec dictionary. -/
theorem selected_public (base : ExternalTypes) (i : PV_Src_NativeInput.Input) :
    PV_Join_FixtureInputs.publicInput base i = publicInput base (PV_Src_NativeInput.publicInput i) := by
  cases i with
  | mk request witness change lane snapshot compiled => cases request <;> rfl

theorem public_eq (base : ExternalTypes) (a b : PV_Src_NativeInput.Input)
    (same : PV_Src_NativeInput.publicInput a = PV_Src_NativeInput.publicInput b) :
    PV_Join_FixtureInputs.publicInput base a = PV_Join_FixtureInputs.publicInput base b := by
  rw [selected_public,selected_public,same]

def unTransition (base : ExternalTypes)
    (t : @aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1
      (PV_Join_PublicCaller.native base)) : BuilderPublicProjection.Transition := by
  letI : ExternalTypes := PV_Join_PublicCaller.native base
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

def unTransfer (p : PV_RunJoin_NominalPublicData.TargetTransfer) : BuilderPublicProjection.Transfer := {
  pool := p.pool
  deployment_domain := p.deployment_domain
  anchor_sequence := p.anchor_sequence
  anchor_root := p.anchor_root
  nullifier := p.nullifier
  asset_id := p.asset_id
  recipient_commitment := p.recipient_commitment
  change_commitment := p.change_commitment }

def unWithdrawal (p : PV_RunJoin_NominalPublicData.TargetWithdrawal) : BuilderPublicProjection.Withdrawal := {
  pool := p.pool
  deployment_domain := p.deployment_domain
  anchor_sequence := p.anchor_sequence
  anchor_root := p.anchor_root
  nullifier := p.nullifier
  asset_id := p.asset_id
  amount := p.amount
  destination_token_account := p.destination_token_account
  change_commitment := p.change_commitment }

def unPublicInput (base : ExternalTypes)
    (p : @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
      (PV_Join_PublicCaller.native base)) : PV_Src_Public.Input := by
  letI : ExternalTypes := PV_Join_PublicCaller.native base
  exact match p with
  | .Transfer pub t => .transfer (unTransfer pub) (unTransition base t)
  | .Withdrawal pub t => .withdrawal (unWithdrawal pub) (unTransition base t)

theorem public_roundtrip (base : ExternalTypes) (p : PV_Src_Public.Input) :
    unPublicInput base (publicInput base p) = p := by
  cases p <;> rfl

/-- Exact criterion: source public binding is necessary as well as sufficient.
In particular the selected compiled transition cannot be silently discarded. -/
theorem public_iff (base : ExternalTypes) (a b : PV_Src_NativeInput.Input) :
    PV_Join_FixtureInputs.publicInput base a = PV_Join_FixtureInputs.publicInput base b ↔
    PV_Src_NativeInput.publicInput a = PV_Src_NativeInput.publicInput b := by
  constructor
  · intro same
    rw [selected_public,selected_public] at same
    have restored := congrArg (unPublicInput base) same
    simpa only [public_roundtrip] using restored
  · exact public_eq base a b

/-- This is the remaining source public-binding fact, not a compiler theorem.
The compilation and its private columns remain those of the SAME record. -/
theorem common_public (base : ExternalTypes) {N C : Type}
    (ops : PV_Join_LedgerSource.World base N C → @ExternalFuns (PV_Join_PublicCaller.native base))
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (a b : PV_Src_NativeInput.Input)
    (same : PV_Src_NativeInput.publicInput a = PV_Src_NativeInput.publicInput b)
    (s : PV_Join_LedgerSource.World base N C) :
    letI : ExternalTypes := PV_Join_PublicCaller.native base
    (PV_Join_FixtureInputs.inputs base ops hash a).ops s =
      (PV_Join_FixtureInputs.inputs base ops hash b).ops s ∧
    (PV_Join_FixtureInputs.inputs base ops hash a).pub s =
      (PV_Join_FixtureInputs.inputs base ops hash b).pub s ∧
    (PV_Join_FixtureInputs.inputs base ops hash a).hash s =
      (PV_Join_FixtureInputs.inputs base ops hash b).hash s := by
  letI : ExternalTypes := PV_Join_PublicCaller.native base
  exact ⟨rfl,public_eq base a b same,rfl⟩

theorem installed_identity (base : ExternalTypes) {N C : Type}
    (ops : PV_Join_LedgerSource.World base N C → @ExternalFuns (PV_Join_PublicCaller.native base))
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (i : PV_Src_NativeInput.Input) (s : PV_Join_LedgerSource.World base N C) :
    letI : ExternalTypes := PV_Join_PublicCaller.native base
    PV_RunJoin_MapErrInstalled.Identity ((PV_Join_FixtureInputs.inputs base ops hash i).ops s) :=
  identity base (ops s)

#print axioms identity
#print axioms selected_public
#print axioms public_eq
#print axioms public_roundtrip
#print axioms public_iff
#print axioms common_public
#print axioms installed_identity
end R1Z.PV_RunJoin_JoinedInstallation
