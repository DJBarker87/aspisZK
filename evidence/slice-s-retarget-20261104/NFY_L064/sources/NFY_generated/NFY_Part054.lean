import Lean
import NFY_Part053
import NBH_Frontier
import NFY_Part005
import NBH_ArrayEq
import NFY_Part024

-- BEGIN copied NED_EncoderLoopCohorts: evidence/slice-s-compose-20261029/NED_EncoderLoopCohorts.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NED_EncoderLoopCohorts
open Aeneas Aeneas.Std Result
abbrev Iter := core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter (Array U32 8#usize))

theorem after_body (iter : Iter) (out : Array U8 688#usize) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1_loop.body iter out =
    AspisR1TerminalDecoder.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1_loop.body iter out := by rfl

theorem after_loop (iter : Iter) (out : Array U8 688#usize) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1_loop iter out =
    AspisR1TerminalDecoder.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1_loop iter out := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1_loop
    AspisR1TerminalDecoder.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1_loop
  have body : (fun (p : Iter × Array U8 688#usize) => AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1_loop.body p.1 p.2) =
      (fun p => AspisR1TerminalDecoder.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1_loop.body p.1 p.2) := by
    funext p; exact after_body p.1 p.2
  rw [body]

theorem live_body (iter : Iter) (out : Slice U8) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1_loop.body iter out =
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1_loop.body iter out := by rfl

theorem live_loop (iter : Iter) (out : Slice U8) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1_loop iter out =
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1_loop iter out := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1_loop
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1_loop
  have body : (fun (p : Iter × Slice U8) => AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1_loop.body p.1 p.2) =
      (fun p => AspisR1TerminalDecoder.pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1_loop.body p.1 p.2) := by
    funext p; exact live_body p.1 p.2
  rw [body]

#print axioms after_body
#print axioms after_loop
#print axioms live_body
#print axioms live_loop
end NFY_NED_EncoderLoopCohorts
-- END copied NED_EncoderLoopCohorts
-- BEGIN copied NED_AfterEncodingConstants: evidence/slice-s-compose-20261029/NED_AfterEncodingConstants.lean
set_option autoImplicit false
namespace NFY_NED_AfterEncodingConstants

theorem magic : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC =
    AspisR1TerminalDecoder.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC AspisR1TerminalDecoder.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC
  rfl

theorem transport_version : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION =
    AspisR1TerminalDecoder.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION AspisR1TerminalDecoder.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION
  rfl

theorem storage_version : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION =
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION
  rfl

theorem digest_version : AspisR1AdapterReconstruct.aspis_statement.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION =
    AspisR1TerminalDecoder.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION AspisR1TerminalDecoder.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION
  rfl

#print axioms magic
#print axioms transport_version
#print axioms storage_version
#print axioms digest_version
end NFY_NED_AfterEncodingConstants
-- END copied NED_AfterEncodingConstants
-- BEGIN copied NED_LiveEncodingConstants: evidence/slice-s-compose-20261029/NED_LiveEncodingConstants.lean
set_option autoImplicit false
namespace NFY_NED_LiveEncodingConstants

theorem magic : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC =
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC
  rfl

theorem version : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION =
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION
  rfl

theorem size : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES =
    800#usize := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
  rfl

theorem depth : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_DEPTH =
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_DEPTH := by
  simp only [AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_DEPTH,
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_DEPTH,
    AspisR1TerminalDecoder.pool_v1.format.POOL_V1_TREE_DEPTH]

theorem note_depth : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_NOTE_DEPTH =
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_NOTE_DEPTH := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_NOTE_DEPTH
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_NOTE_DEPTH
  rw [depth]

theorem sentinel : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_SECOND_SENTINEL_LANE =
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_SECOND_SENTINEL_LANE := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_SECOND_SENTINEL_LANE
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_SECOND_SENTINEL_LANE
  rfl

theorem format : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_FORMAT_BINDING =
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_FORMAT_BINDING := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_FORMAT_BINDING
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_FORMAT_BINDING
  rw [depth,note_depth,sentinel]
  simp only [NFY_NED_AfterEncodingConstants.storage_version]

#print axioms magic
#print axioms version
#print axioms size
#print axioms depth
#print axioms note_depth
#print axioms sentinel
#print axioms format
end NFY_NED_LiveEncodingConstants
-- END copied NED_LiveEncodingConstants
-- BEGIN copied NED_RawCarrierInverses: evidence/slice-s-compose-20261029/NED_RawCarrierInverses.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NED_RawCarrierInverses
open NFY_NED_ReconstructCarriers NFY_NED_PaymentCohorts

def fromRawTransfer (p : RT) : T := AspisS6CurrentAdapterCarrier.toPoolV1PrivateTransferPublicV1
  (AspisR1.JHf_Carrier.fromPoolV1PrivateTransferPublicV1 p)
def fromRawWithdrawal (p : RW) : W := AspisS6CurrentAdapterCarrier.toPoolV1WithdrawalPublicV1
  (AspisR1.JHf_Carrier.fromPoolV1WithdrawalPublicV1 p)

theorem common (p : RawCommon) : NFY_NED_ReconstructCarriers.toRawCommon (fromRawCommon p) = p := by
  cases p <;> rfl

theorem transfer (p : RT) : toRawTransfer (fromRawTransfer p) = p := by
  cases p <;> rfl

theorem withdrawal (p : RW) : toRawWithdrawal (fromRawWithdrawal p) = p := by
  cases p <;> rfl

theorem statement (p : Raw) : toRaw (fromRaw p) = p := by
  cases p <;> rfl

#print axioms common
#print axioms transfer
#print axioms withdrawal
#print axioms statement
end NFY_NED_RawCarrierInverses
-- END copied NED_RawCarrierInverses
-- BEGIN copied NED_RawAfterFrontier: evidence/slice-s-compose-20261029/NED_RawAfterFrontier.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NED_RawAfterFrontier
open Aeneas Aeneas.Std Result WP AspisR1AdapterReconstruct
open NBD_DigestInduction NBH_Frontier
attribute [local instance] Classical.propDecidable

theorem afterstate_loop (a : Frontier) :
    aspis_statement.pool_v1.pair_terminal.validate_verified_afterstate_loop a 0#usize =
    ok (if CanonicalFrom a 0 then .Ok () else .Err .NonCanonicalAfterstate) := by
  have spec : aspis_statement.pool_v1.pair_terminal.validate_verified_afterstate_loop a 0#usize
      ⦃ r => r = if CanonicalFrom a 0 then .Ok () else .Err .NonCanonicalAfterstate ⦄ := by
    unfold aspis_statement.pool_v1.pair_terminal.validate_verified_afterstate_loop
    refine loop.spec_decr_nat (fun i : Usize => 20-i.val)
      (fun i : Usize => i.val ≤ 20 ∧ (CanonicalFrom a 0 ↔ CanonicalFrom a i.val))
      (fun r => r = if CanonicalFrom a 0 then .Ok () else .Err .NonCanonicalAfterstate)
      (fun i => aspis_statement.pool_v1.pair_terminal.validate_verified_afterstate_loop.body a i) 0#usize ?_ ?_
    · intro i hi
      rcases hi with ⟨bound,eqv⟩
      unfold aspis_statement.pool_v1.pair_terminal.validate_verified_afterstate_loop.body
      simp only [NFY_NED_ScannerCohorts.profile_result]
      step*
      all_goals simp_all [CanonicalFrom]
      all_goals first | scalar_tac | skip
      · refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        constructor
        · intro h j hj; exact h j (by omega)
        · intro h j hj
          by_cases same : j.val = i.val
          · simpa only [same] using (show Canonical (a.val[i.val]'(by have := a.property; scalar_tac)) from by assumption)
          · exact h j (by omega)
      · refine ⟨⟨i.val, by scalar_tac⟩, Nat.le_refl _, ?_⟩
        assumption
    · exact ⟨by scalar_tac, Iff.rfl⟩
  obtain ⟨r,call,same⟩ := WP.spec_imp_exists spec
  rw [same] at call
  exact call

#print axioms afterstate_loop
end NFY_NED_RawAfterFrontier
-- END copied NED_RawAfterFrontier
-- BEGIN copied NED_RawAfterValidator: evidence/slice-s-compose-20261029/NED_RawAfterValidator.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NED_RawAfterValidator
open Aeneas Aeneas.Std Result WP AspisR1AdapterReconstruct
open NBD_DigestInduction NBH_Frontier
attribute [local instance] Classical.propDecidable
abbrev Afterstate := aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1
abbrev AfterError := aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1

def afterResult (a : Afterstate) : core.result.Result Unit AfterError :=
  if a.next_pair_index.val = 0 ∨ 1048576 < a.next_pair_index.val then .Err .InvalidAfterstateIndex
  else if Canonical a.next_root ∧ CanonicalFrom a.next_frontier 0 then .Ok ()
  else .Err .NonCanonicalAfterstate

theorem afterstate (a : Afterstate) :
    aspis_statement.pool_v1.pair_terminal.validate_verified_afterstate a = ok (afterResult a) := by
  have spec : aspis_statement.pool_v1.pair_terminal.validate_verified_afterstate a
      ⦃ r => r = afterResult a ⦄ := by
    unfold aspis_statement.pool_v1.pair_terminal.validate_verified_afterstate
    rw [NFY_NED_ScannerCohorts.profile_result, NFY_NED_RawAfterFrontier.afterstate_loop]
    unfold aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_CAPACITY
      aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_DEPTH
    step*
    all_goals simp_all [afterResult]
    all_goals scalar_tac
  obtain ⟨r,call,same⟩ := WP.spec_imp_exists spec
  rw [same] at call
  exact call

#print axioms afterstate
end NFY_NED_RawAfterValidator
-- END copied NED_RawAfterValidator
-- BEGIN copied NED_RawLiveFrontier: evidence/slice-s-compose-20261029/NED_RawLiveFrontier.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NED_RawLiveFrontier
open Aeneas Aeneas.Std Result WP AspisR1AdapterReconstruct
open NBD_DigestInduction
attribute [local instance] Classical.propDecidable
open NBH_Frontier

theorem live_loop (a : Frontier) :
    aspis_statement.pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1_loop a 0#usize =
    ok (if CanonicalFrom a 0 then .Ok () else .Err .NonCanonicalDigest) := by
  have spec : aspis_statement.pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1_loop a 0#usize
      ⦃ r => r = if CanonicalFrom a 0 then .Ok () else .Err .NonCanonicalDigest ⦄ := by
    unfold aspis_statement.pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1_loop
    refine loop.spec_decr_nat (fun i : Usize => 20-i.val)
      (fun i : Usize => i.val ≤ 20 ∧ (CanonicalFrom a 0 ↔ CanonicalFrom a i.val))
      (fun r => r = if CanonicalFrom a 0 then .Ok () else .Err .NonCanonicalDigest)
      (fun i => aspis_statement.pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1_loop.body a i) 0#usize ?_ ?_
    · intro i hi
      rcases hi with ⟨bound,eqv⟩
      unfold aspis_statement.pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1_loop.body
      simp only [NFY_NED_ScannerCohorts.profile_result]
      step*
      all_goals simp_all [CanonicalFrom]
      all_goals first | scalar_tac | skip
      · refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        constructor
        · intro h j hj; exact h j (by omega)
        · intro h j hj
          by_cases same : j.val = i.val
          · simpa only [same] using (show Canonical (a.val[i.val]'(by have := a.property; scalar_tac)) from by assumption)
          · exact h j (by omega)
      · refine ⟨⟨i.val, by scalar_tac⟩, Nat.le_refl _, ?_⟩
        assumption
    · exact ⟨by scalar_tac, Iff.rfl⟩
  obtain ⟨r,call,same⟩ := WP.spec_imp_exists spec
  rw [same] at call
  exact call

#print axioms live_loop
end NFY_NED_RawLiveFrontier
-- END copied NED_RawLiveFrontier
-- BEGIN copied NED_RawLiveValidator: evidence/slice-s-compose-20261029/NED_RawLiveValidator.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NED_RawLiveValidator
open Aeneas Aeneas.Std Result WP AspisR1AdapterReconstruct
open NBD_DigestInduction NBH_Frontier
attribute [local instance] Classical.propDecidable
abbrev Snapshot := aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1
abbrev Error := aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1

def result (s : Snapshot) : core.result.Result Unit Error :=
  if s.pool = Array.repeat 32#usize 0#u8 ∨ s.deployment_domain = Array.repeat 32#usize 0#u8 then .Err .ZeroRequiredBinding
  else if s.sequence ≠ s.next_pair_index then .Err .SequenceIndexMismatch
  else if 1048576 ≤ s.next_pair_index.val then .Err .TreeFull
  else if Canonical s.current_root ∧ CanonicalFrom s.frontier 0 then .Ok ()
  else .Err .NonCanonicalDigest

theorem source (s : Snapshot) :
    aspis_statement.pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1 s = ok (result s) := by
  have spec : aspis_statement.pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1 s
      ⦃ r => r = result s ⦄ := by
    unfold aspis_statement.pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1
    rw [NFY_NED_ScannerCohorts.profile_result, NFY_NED_RawLiveFrontier.live_loop]
    simp only [NBH_ArrayEq.source]
    unfold aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_CAPACITY
      aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_DEPTH
    step*
    all_goals simp_all [result]
    all_goals scalar_tac
  obtain ⟨r,call,same⟩ := WP.spec_imp_exists spec
  rw [same] at call
  exact call

#print axioms source
end NFY_NED_RawLiveValidator
-- END copied NED_RawLiveValidator
-- BEGIN copied NED_LateCarriers: evidence/slice-s-compose-20261029/NED_LateCarriers.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NED_LateCarriers
open Aeneas Aeneas.Std Result
abbrev TSnapshot := AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1
abbrev TAfter := AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1
abbrev TLate := AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1
abbrev RSnapshot := AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1
abbrev RAfter := AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1
abbrev RLate := AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1

def toRawSnapshot (s : TSnapshot) : RSnapshot := AspisR1.JHf_Carrier.toPoolV1PairLiveSnapshotV1
  (AspisS6CurrentAdapterCarrier.fromPoolV1PairLiveSnapshotV1 s)
def fromRawSnapshot (s : RSnapshot) : TSnapshot := AspisS6CurrentAdapterCarrier.toPoolV1PairLiveSnapshotV1
  (AspisR1.JHf_Carrier.fromPoolV1PairLiveSnapshotV1 s)
def toRawAfter (s : TAfter) : RAfter := AspisR1.JHf_Carrier.toPoolV1PairVerifiedAfterstateV1
  (AspisS6CurrentAdapterCarrier.fromPoolV1PairVerifiedAfterstateV1 s)
def fromRawAfter (s : RAfter) : TAfter := AspisS6CurrentAdapterCarrier.toPoolV1PairVerifiedAfterstateV1
  (AspisR1.JHf_Carrier.fromPoolV1PairVerifiedAfterstateV1 s)
def toRawLate (s : TLate) : RLate := AspisR1.JHf_Carrier.toPoolV1PairLatePublicStatementV1
  (AspisS6CurrentAdapterCarrier.fromPoolV1PairLatePublicStatementV1 s)
def fromRawLate (s : RLate) : TLate := AspisS6CurrentAdapterCarrier.toPoolV1PairLatePublicStatementV1
  (AspisR1.JHf_Carrier.fromPoolV1PairLatePublicStatementV1 s)

theorem snapshot_to_from (s : RSnapshot) : toRawSnapshot (fromRawSnapshot s) = s := by cases s <;> rfl
theorem snapshot_from_to (s : TSnapshot) : fromRawSnapshot (toRawSnapshot s) = s := by cases s <;> rfl
theorem after_to_from (s : RAfter) : toRawAfter (fromRawAfter s) = s := by cases s <;> rfl
theorem after_from_to (s : TAfter) : fromRawAfter (toRawAfter s) = s := by cases s <;> rfl
theorem late_to_from (s : RLate) : toRawLate (fromRawLate s) = s := by cases s <;> rfl
theorem late_from_to (s : TLate) : fromRawLate (toRawLate s) = s := by cases s <;> rfl

#print axioms snapshot_to_from
#print axioms snapshot_from_to
#print axioms after_to_from
#print axioms after_from_to
#print axioms late_to_from
#print axioms late_from_to
end NFY_NED_LateCarriers
-- END copied NED_LateCarriers
-- BEGIN copied NED_LateValidatorCohorts: evidence/slice-s-compose-20261029/NED_LateValidatorCohorts.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NED_LateValidatorCohorts
open Aeneas Aeneas.Std Result NFY_NED_LateCarriers NFY_NED_ErrorCarriers
attribute [local instance] Classical.propDecidable

def mapResult {α E F : Type} (f : E → F) : core.result.Result α E → core.result.Result α F
  | .Ok x => .Ok x
  | .Err e => .Err (f e)

theorem after (s : TAfter) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.validate_verified_afterstate (toRawAfter s) =
    ok (mapResult toRawPoolV1PairVerifierTransportErrorV1 (NFY_NBH_Validators.afterResult s)) := by
  rw [NFY_NED_RawAfterValidator.afterstate]
  simp only [NFY_NED_RawAfterValidator.afterResult, NFY_NBH_Validators.afterResult, toRawAfter,
    AspisR1.JHf_Carrier.toPoolV1PairVerifiedAfterstateV1,
    AspisS6CurrentAdapterCarrier.fromPoolV1PairVerifiedAfterstateV1]
  repeat' split
  all_goals simp_all [mapResult,toRawPoolV1PairVerifierTransportErrorV1]

theorem snapshot (s : TSnapshot) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1 (toRawSnapshot s) =
    ok (mapResult toRawPoolV1PairLiveSnapshotErrorV1 (NFY_NBH_LiveValidator.result s)) := by
  rw [NFY_NED_RawLiveValidator.source]
  simp only [NFY_NED_RawLiveValidator.result, NFY_NBH_LiveValidator.result, toRawSnapshot,
    AspisR1.JHf_Carrier.toPoolV1PairLiveSnapshotV1,
    AspisS6CurrentAdapterCarrier.fromPoolV1PairLiveSnapshotV1]
  repeat' split
  all_goals simp_all [mapResult,toRawPoolV1PairLiveSnapshotErrorV1]

#print axioms after
#print axioms snapshot
end NFY_NED_LateValidatorCohorts
-- END copied NED_LateValidatorCohorts
-- BEGIN copied NED_AfterEncodingCohort: evidence/slice-s-compose-20261029/NED_AfterEncodingCohort.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NED_AfterEncodingCohort
open Aeneas Aeneas.Std Result NFY_NED_LateCarriers NFY_NED_LateValidatorCohorts NFY_NED_ErrorCarriers
open AspisR1.S2K

def mapOuter {α E F : Type} (f : E → F) : Result (core.result.Result α E) → Result (core.result.Result α F)
 | .ok r => .ok (mapResult f r)
 | .fail e => .fail e
 | .div => .div

/-- Reuse the symbolic bounded-store and frontier-fold theorems; no concrete
688-byte prefix or entire loop is evaluated by definitional equality. -/
theorem result (s : TAfter) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 (toRawAfter s) =
    mapOuter toRawPoolV1PairVerifierTransportErrorV1
      (AspisR1TerminalDecoder.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 s) := by
  rw [NFY_NBK_AfterstateResult.source]
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1
  rw [NFY_NED_LateValidatorCohorts.after]
  cases valid : NFY_NBH_Validators.afterResult s with
  | Err e => simp [mapResult,mapOuter,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame]
  | Ok u =>
    cases u
    simp only [mapResult,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,mapOuter]
    simp only [toRawAfter,AspisR1.JHf_Carrier.toPoolV1PairVerifiedAfterstateV1,
      AspisS6CurrentAdapterCarrier.fromPoolV1PairVerifiedAfterstateV1,
      NFY_NED_DigestCohorts.digest_encode,NFY_NED_EncoderLoopCohorts.after_loop,
      NFY_NED_AfterEncodingConstants.magic,NFY_NED_AfterEncodingConstants.transport_version,
      NFY_NED_AfterEncodingConstants.storage_version,NFY_NED_AfterEncodingConstants.digest_version]
    unfold AfterstateEncoding.bytes
    generalize Array.repeat 688#usize 0#u8 = output
    change AfterstatePrepare.run s output (fun iter out => do
      let encoded ← AspisR1TerminalDecoder.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1_loop iter out
      ok (core.result.Result.Ok encoded)) = _
    rw [AfterstatePrepare.exact]
    rw [AfterstateBytes.loop_exact s.next_frontier 0#usize (by decide)]
    rfl

#print axioms result
end NFY_NED_AfterEncodingCohort
-- END copied NED_AfterEncodingCohort
-- BEGIN copied NED_LiveEncodingCohort: evidence/slice-s-compose-20261029/NED_LiveEncodingCohort.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NED_LiveEncodingCohort
open Aeneas Aeneas.Std Result NFY_NED_LateCarriers NFY_NED_LateValidatorCohorts NFY_NED_ErrorCarriers

def mapStateOuter {α E F State : Type} (f : E → F) :
    Result (core.result.Result α E × State) → Result (core.result.Result α F × State)
 | .ok (r,st) => .ok (mapResult f r,st)
 | .fail e => .fail e
 | .div => .div

theorem result (s : TSnapshot) (out : Slice U8) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1 (toRawSnapshot s) out =
    mapStateOuter toRawPoolV1PairLiveSnapshotErrorV1
      (AspisR1TerminalDecoder.pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1 s out) := by
  rw [NFY_NBK_LiveResult.source]
  by_cases size : out.length = 800
  · rw [if_neg (not_not.mpr size)]
    have len : Slice.len out = 800#usize := by scalar_tac
    unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1
    simp only [NFY_NED_LiveEncodingConstants.size,len,bne_self_eq_false,if_false]
    rw [NFY_NED_LateValidatorCohorts.snapshot]
    cases valid : NFY_NBH_LiveValidator.result s with
    | Err e => simp [mapResult,mapStateOuter,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame]
    | Ok u =>
      cases u
      simp only [mapResult,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,mapStateOuter]
      simp only [toRawSnapshot,AspisR1.JHf_Carrier.toPoolV1PairLiveSnapshotV1,
        AspisS6CurrentAdapterCarrier.fromPoolV1PairLiveSnapshotV1,
        NFY_NED_DigestCohorts.digest_encode,NFY_NED_EncoderLoopCohorts.live_loop,
        NFY_NED_LiveEncodingConstants.magic,NFY_NED_LiveEncodingConstants.version,NFY_NED_LiveEncodingConstants.format]
      have fill : core.slice.Slice.fill core.clone.CloneU8 out 0#u8 = ok NFY_NBK_LiveResult.zero := by
        rw [NFY_NBK_Fill.source]
        congr 1
        apply Subtype.ext
        change List.replicate out.length 0#u8 = List.replicate 800 0#u8
        rw [size]
      rw [fill]
      simp only [bind_tc_ok]
      have zero_size : NFY_NBK_LiveResult.zero.length = 800 := by
        simp only [NFY_NBK_LiveResult.zero,Slice.length,Array.to_slice,Array.repeat_val,List.length_replicate]
        rfl
      have prepared_size : (NFY_NBK_LivePrepare.value s NFY_NBK_LiveResult.zero).length = 800 := by
        simp only [NFY_NBK_LivePrepare.value,Slice.length,NFY_NBK_LiveResult.zero,Array.to_slice,Array.repeat_val,
          List.length_setSlice!,List.length_set,List.length_replicate]
        rfl
      change NFY_NBK_LivePrepare.run s NFY_NBK_LiveResult.zero (fun iter bytes => do
        let encoded ← AspisR1TerminalDecoder.pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1_loop iter bytes
        ok (core.result.Result.Ok (),encoded)) = _
      rw [NFY_NBK_LivePrepare.exact s NFY_NBK_LiveResult.zero zero_size]
      rw [NFY_NBK_LiveBytes.loop_exact s.frontier 0#usize (by decide) _ prepared_size]
      rfl
  · rw [if_pos size]
    have len : Slice.len out ≠ 800#usize := by scalar_tac
    simp only [AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1,
      NFY_NED_LiveEncodingConstants.size,ne_eq,bne_iff_ne,len,not_false_eq_true,if_true,mapStateOuter,mapResult,
      toRawPoolV1PairLiveSnapshotErrorV1]

#print axioms result
end NFY_NED_LiveEncodingCohort
-- END copied NED_LiveEncodingCohort
-- BEGIN copied NED_RawLateTail: evidence/slice-s-compose-20261029/NED_RawLateTail.lean
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace NFY_NED_RawLateTail
open Aeneas Aeneas.Std Result AspisR1.S2K
open AspisR1AdapterReconstruct.aspis_statement
open pool_v1.pair_tree_profile
abbrev Statement := NFY_NED_LateCarriers.TLate
abbrev Error := PoolV1PairLatePublicStatementErrorV1

def run (s : Statement) (output : Slice U8) :
    Result (core.result.Result Unit Error × Slice U8) := do
  let i7 ← 32#usize + POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
  let (s15, back) ← core.slice.index.Slice.index_mut
    (core.slice.index.SliceIndexRangeUsizeSlice U8) output {start := 32#usize, «end» := i7}
  let (r, s16) ← encode_pool_v1_pair_live_snapshot_v1 (NFY_NED_LateCarriers.toRawSnapshot s.live_snapshot) s15
  match r with
  | .Err e => ok (.Err (.Snapshot e), back s16)
  | .Ok _ =>
    let r2 ← pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 (NFY_NED_LateCarriers.toRawAfter s.candidate_afterstate)
    match r2 with
    | .Err e => ok (.Err (.Afterstate e), back s16)
    | .Ok bytes =>
      let (dest, back2) ← core.slice.index.Slice.index_mut
        (core.slice.index.SliceIndexRangeFromUsizeSlice U8) (back s16) {start := i7}
      let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 dest bytes.to_slice
      ok (.Ok (), back2 copied)

 theorem exact (s : Statement) (output : Slice U8) (size : output.length = 1520) :
    run s output = ok (NFY_NED_LateValidatorCohorts.mapResult NFY_NED_ErrorCarriers.toRawPoolV1PairLatePublicStatementErrorV1
      (NFY_NBN_LateTail.status s), NFY_NBN_LateTail.value s output) := by
  have len : output.val.length = 1520 := size
  unfold run
  simp only [NFY_NED_LiveEncodingConstants.size]
  have add : 32#usize + 800#usize = ok 832#usize := by
    have h : (32#usize + 800#usize) ⦃ r => r = 832#usize ⦄ := by step*
    obtain ⟨r, call, same⟩ := WP.spec_imp_exists h
    exact same ▸ call
  rw [add]
  simp only [bind_tc_ok]
  simp [core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut, Slice.length,Slice.len,len]
  rw [NFY_NED_LiveEncodingCohort.result,NFY_NBK_LiveResult.source]
  simp [Slice.length, Slice.slice,List.slice,len]
  cases hv : NFY_NBH_LiveValidator.result s.live_snapshot with
  | Err e =>
    simp [NFY_NED_LiveEncodingCohort.mapStateOuter,NFY_NED_AfterEncodingCohort.mapOuter,NFY_NED_LateValidatorCohorts.mapResult,NFY_NED_ErrorCarriers.toRawPoolV1PairLatePublicStatementErrorV1,hv,NFY_NBN_LateTail.status,NFY_NBN_LateTail.value,bind_tc_ok]
    apply Subtype.ext
    simp only [List.setSlice!,List.length_take,List.length_drop,len]
    simp only [show min 800 (1520-32) = 800 by decide,
      show min 800 (min 800 (1520-32)) = 800 by decide]
    simp only [List.take_take,Nat.min_self]
    have restored := List.take_append_drop 800 (output.val.drop 32)
    simp only [List.drop_drop] at restored
    simpa only [List.append_assoc, restored, List.take_append_drop]
  | Ok u =>
    cases u
    simp only [hv,bind_tc_ok,NFY_NED_LiveEncodingCohort.mapStateOuter,NFY_NED_LateValidatorCohorts.mapResult]
    rw [NFY_NED_AfterEncodingCohort.result,NFY_NBK_AfterstateResult.source]
    cases ha : NFY_NBH_Validators.afterResult s.candidate_afterstate with
    | Err e => simp [NFY_NED_LiveEncodingCohort.mapStateOuter,NFY_NED_AfterEncodingCohort.mapOuter,NFY_NED_LateValidatorCohorts.mapResult,NFY_NED_ErrorCarriers.toRawPoolV1PairLatePublicStatementErrorV1,ha,NFY_NBN_LateTail.status,NFY_NBN_LateTail.value,hv,bind_tc_ok,Slice.setSlice!]
    | Ok u =>
      cases u
      simp [NFY_NED_LiveEncodingCohort.mapStateOuter,NFY_NED_AfterEncodingCohort.mapOuter,NFY_NED_LateValidatorCohorts.mapResult,NFY_NED_ErrorCarriers.toRawPoolV1PairLatePublicStatementErrorV1,ha,hv,NFY_NBN_LateTail.status,NFY_NBN_LateTail.value,bind_tc_ok,
        core.slice.index.Slice.index_mut,core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut,
        core.slice.Slice.copy_from_slice,Array.to_slice,Slice.length,Slice.len,
        Slice.slice,List.slice,List.length_setSlice!,len,NFY_NBN_LateTail.live_length,
        (AfterstateEncoding.bytes s.candidate_afterstate).property,Slice.setSlice!,lift]

#print axioms exact
end NFY_NED_RawLateTail
-- END copied NED_RawLateTail
-- BEGIN copied NED_LateEncodingConstants: evidence/slice-s-compose-20261029/NED_LateEncodingConstants.lean
set_option autoImplicit false
namespace NFY_NED_LateEncodingConstants

theorem magic : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC =
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC
  rfl

theorem version : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_VERSION =
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_VERSION := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_VERSION
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_VERSION
  rfl

theorem items : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_ITEM_COUNT =
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_ITEM_COUNT := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_ITEM_COUNT
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_ITEM_COUNT
  rfl

theorem header : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES =
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES
  rfl

theorem live_bytes : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES =
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES := by
  rw [NFY_NED_LiveEncodingConstants.size]
  unfold AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
  rfl

theorem after_bytes : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES =
    AspisR1TerminalDecoder.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES := by
  simp only [AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES,
    AspisR1TerminalDecoder.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES,
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES,
    AspisR1TerminalDecoder.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES]

theorem size_eq : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES =
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES
  rw [header,live_bytes,after_bytes]

theorem size : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES =
    Aeneas.Std.Result.ok 1520#usize := by
  rw [size_eq,AspisR1.NFY_JFs_LateConstants.size]

#print axioms magic
#print axioms version
#print axioms items
#print axioms header
#print axioms live_bytes
#print axioms after_bytes
#print axioms size_eq
#print axioms size
end NFY_NED_LateEncodingConstants
-- END copied NED_LateEncodingConstants
-- BEGIN copied NED_LateCarrierFields: evidence/slice-s-compose-20261029/NED_LateCarrierFields.lean
set_option autoImplicit false
namespace NFY_NED_LateCarrierFields
open NFY_NED_LateCarriers NFY_NED_ReconstructCarriers

theorem live (s : TLate) : (toRawLate s).live_snapshot = toRawSnapshot s.live_snapshot := by rfl
theorem after (s : TLate) : (toRawLate s).candidate_afterstate = toRawAfter s.candidate_afterstate := by rfl
theorem live_index (s : TSnapshot) : (toRawSnapshot s).next_pair_index = s.next_pair_index := by rfl
theorem after_index (s : TAfter) : (toRawAfter s).next_pair_index = s.next_pair_index := by rfl
theorem live_frontier (s : TSnapshot) : (toRawSnapshot s).frontier = s.frontier := by rfl
theorem after_frontier (s : TAfter) : (toRawAfter s).next_frontier = s.next_frontier := by rfl
theorem common_late (s : Common) : (NFY_NED_ReconstructCarriers.toRawCommon s).lane_transition = toRawLate s.lane_transition := by rfl
theorem common_anchor (s : Common) : (NFY_NED_ReconstructCarriers.toRawCommon s).historical_global_anchor = s.historical_global_anchor := by rfl

#print axioms live
#print axioms after
#print axioms live_index
#print axioms after_index
#print axioms live_frontier
#print axioms after_frontier
#print axioms common_late
#print axioms common_anchor
end NFY_NED_LateCarrierFields
-- END copied NED_LateCarrierFields
-- BEGIN copied NED_RawLateFactor: evidence/slice-s-compose-20261029/NED_RawLateFactor.lean
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open Aeneas Aeneas.Std Result
namespace NFY_NED_RawLateFactor
open AspisR1AdapterReconstruct
open aspis_statement
open pool_v1.pair_tree_profile

def raw (statement : NFY_NED_LateCarriers.TLate) (output : Slice U8) :
    Result (core.result.Result Unit PoolV1PairLatePublicStatementErrorV1 × Slice U8) := do
      let i7 ← 32#usize + pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
      let (s15, index_mut_back5) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output { start := 32#usize, «end» := i7 }
      let (r, s16) ← pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1 (NFY_NED_LateCarriers.toRawSnapshot statement.live_snapshot) s15
      let r1 ← AspisR1AdapterReconstruct.core.result.Result.map_err pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLiveSnapshotErrorV1PoolV1PairLatePublicStatementErrorV1 r ()
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let r2 ← pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 (NFY_NED_LateCarriers.toRawAfter statement.candidate_afterstate)
        let r3 ← AspisR1AdapterReconstruct.core.result.Result.map_err pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1PoolV1PairLatePublicStatementErrorV1 r2 ()
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue val => let output9 := index_mut_back5 s16
                                                            let (s17, index_mut_back6) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8) output9 { start := i7 }
                                                            let s18 ← lift (Array.to_slice val)
                                                            let s19 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s17 s18
                                                            let output10 := index_mut_back6 s19
                                                            ok (core.result.Result.Ok (), output10)
        | core.ops.control_flow.ControlFlow.Break residual => let r4 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) residual
                                                              let output9 := index_mut_back5 s16
                                                              ok (r4, output9)
      | core.ops.control_flow.ControlFlow.Break residual => let r2 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) residual
                                                            let output9 := index_mut_back5 s16
                                                            ok (r2, output9)


theorem raw_eq (s : NFY_NED_LateCarriers.TLate) (output : Slice U8) :
    raw s output = NFY_NED_RawLateTail.run s output := by
  unfold raw NFY_NED_RawLateTail.run
  apply NFY_NBN_LateFactor.bind_ext
  intro i7
  apply NFY_NBN_LateFactor.bind_ext
  intro window
  rcases window with ⟨input,back⟩
  apply NFY_NBN_LateFactor.bind_ext
  intro child
  rcases child with ⟨r,live⟩
  cases r with
  | Err e => rfl
  | Ok u =>
    cases u
    dsimp only [Aeneas.Std.uncurry]
    simp only [AspisR1AdapterReconstruct.core.result.Result.map_err,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTry.branch]
    apply NFY_NBN_LateFactor.bind_ext
    intro after
    cases after <;> rfl

#print axioms raw_eq
end NFY_NED_RawLateFactor
-- END copied NED_RawLateFactor

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
