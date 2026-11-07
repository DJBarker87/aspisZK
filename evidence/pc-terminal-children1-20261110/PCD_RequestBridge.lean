import PCD_RequestEmitter
import PCD_RequestRef
set_option autoImplicit false
noncomputable section
namespace PCD_RequestBridge
open Aeneas Aeneas.Std PCD_FrozenRequest

theorem reference_eq_emitted (bytes : Slice U8) :
    request_ref bytes = pair_forest.decode_terminal_request_box_v1 bytes := by
  rw [PCD_RequestEmitter.emitted_complete]
  unfold request_ref
    PCD_FrozenRequest.aspis_statement.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_v1
    PCD_RequestEmitter.continuation
  cases h : NFY_NFD_RequestOracle.runSlice bytes with
  | ok decoded => cases decoded <;> rfl
  | fail error => rfl
  | div => rfl

/-- Inverse structural carrier at every local value, both payment branches. -/
theorem local_roundtrip (x : LocalRequest) : mapRequest (unmapRequest x) = x := by
  cases x with
  | mk profile release program payment =>
    cases payment with
    | PrivateTransfer p => cases p; rfl
    | Withdrawal p => cases p; rfl

def toCohortPoolV1PrivateTransferPublicV1 (x : aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : AspisR20Request.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 := {
  pool := x.pool
  deployment_domain := x.deployment_domain
  anchor_sequence := x.anchor_sequence
  anchor_root := x.anchor_root
  nullifier := x.nullifier
  asset_id := x.asset_id
  recipient_commitment := x.recipient_commitment
  change_commitment := x.change_commitment
}

def fromCohortPoolV1PrivateTransferPublicV1 (x : AspisR20Request.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 := {
  pool := x.pool
  deployment_domain := x.deployment_domain
  anchor_sequence := x.anchor_sequence
  anchor_root := x.anchor_root
  nullifier := x.nullifier
  asset_id := x.asset_id
  recipient_commitment := x.recipient_commitment
  change_commitment := x.change_commitment
}

def toCohortPoolV1WithdrawalPublicV1 (x : aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : AspisR20Request.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 := {
  pool := x.pool
  deployment_domain := x.deployment_domain
  anchor_sequence := x.anchor_sequence
  anchor_root := x.anchor_root
  nullifier := x.nullifier
  asset_id := x.asset_id
  amount := x.amount
  destination_token_account := x.destination_token_account
  change_commitment := x.change_commitment
}

def fromCohortPoolV1WithdrawalPublicV1 (x : AspisR20Request.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 := {
  pool := x.pool
  deployment_domain := x.deployment_domain
  anchor_sequence := x.anchor_sequence
  anchor_root := x.anchor_root
  nullifier := x.nullifier
  asset_id := x.asset_id
  amount := x.amount
  destination_token_account := x.destination_token_account
  change_commitment := x.change_commitment
}

def toCohort (x : LocalRequest) : NFY_NFD_RequestProjection.Request := {
  verifier_profile := x.verifier_profile,verifier_release := x.verifier_release,pool_program := x.pool_program,
  «public» := match x.«public» with
    | .PrivateTransfer p => .PrivateTransfer (toCohortPoolV1PrivateTransferPublicV1 p)
    | .Withdrawal p => .Withdrawal (toCohortPoolV1WithdrawalPublicV1 p)
}
def fromCohort (x : NFY_NFD_RequestProjection.Request) : LocalRequest := {
  verifier_profile := x.verifier_profile,verifier_release := x.verifier_release,pool_program := x.pool_program,
  «public» := match x.«public» with
    | .PrivateTransfer p => .PrivateTransfer (fromCohortPoolV1PrivateTransferPublicV1 p)
    | .Withdrawal p => .Withdrawal (fromCohortPoolV1WithdrawalPublicV1 p)
}
theorem cohort_roundtrip (x : LocalRequest) : fromCohort (toCohort x) = x := by
  cases x with
  | mk profile release program payment =>
    cases payment with
    | PrivateTransfer p => cases p; rfl
    | Withdrawal p => cases p; rfl

def observation (value : LocalRequest) (slot : Fin 14) (word : Fin 8) (byte : Fin 32) : Nat :=
  NFY_NFD_RequestProjection.project (toCohort value) slot word byte

theorem observations_complete (x y : LocalRequest)
    (same : ∀ slot word byte, observation x slot word byte = observation y slot word byte) : x = y := by
  have h := NFY_NFD_RequestProjection.complete (toCohort x) (toCohort y) same
  have mapped := congrArg fromCohort h
  simpa only [cohort_roundtrip] using mapped
#print axioms cohort_roundtrip

/-- The native sampler casts byte indices to usize. This is surjective over
its entire stated <32 domain, so no caller precondition was strengthened. -/
def indexWord (n : Nat) : U8 := ⟨BitVec.ofNat 8 n⟩
theorem index_sampler_complete (n : Nat) (bounded : n < 32) :
    (indexWord n).val = n := by
  change (BitVec.ofNat 8 n).toNat = n
  simp only [BitVec.toNat_ofNat]
  omega
#print axioms index_sampler_complete
#print axioms reference_eq_emitted
#print axioms local_roundtrip
#print axioms observations_complete
end PCD_RequestBridge
