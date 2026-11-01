import PV_BR_Transport

/-! D540: transport the actual successful-admission premise used by
BuilderAdmissionRecords.words_of_common_success. Prover/runtime failures and
divergence remain explicit. This file is a draft until the recorded compile. -/
set_option autoImplicit false
namespace PV_BR_AdmissionTransport
open Aeneas Aeneas.Std
open PV_BR_Transport

/-- Privacy-owned envelope, from pair_trace.rs 136:0-159:1. Its statement/tree
payloads use the immutable NDR declarations through proved transport. -/
inductive AdmissionError where
  | Statement : paymentShared → AdmissionError
  | PairLeaf : AspisBuilderAdmissionSource.pool_v1.pair_tree_profile.PoolV1PairLeafErrorV1 → AdmissionError
  | Tree : treeShared → AdmissionError
  | Shape : AdmissionError
  | WrongVariant : AdmissionError
  | RuntimeBinding : AdmissionError
  | NullifierAlreadySpent : AdmissionError
  | WitnessDigest : AdmissionError
  | ValueOutOfRange : AdmissionError
  | Conservation : AdmissionError
  | HashSchedule : AdmissionError
  | SelectedCommitmentMismatch : AdmissionError
  | AnchorMismatch : AdmissionError
  | NullifierMismatch : AdmissionError
  | RecipientCommitmentMismatch : AdmissionError
  | ChangeCommitmentMismatch : AdmissionError
  | SnapshotBindingMismatch : AdmissionError
  | BlockMismatch : U8 → U8 → U8 → AdmissionError
  | AuxiliaryMismatch : U16 → U8 → AdmissionError
  | MetadataMismatch : AdmissionError
  | CopyLayout : AdmissionError
  | CopyImbalance : AdmissionError

def toShared : AspisBuilderAdmissionSource.pool_v1.pair_trace.PoolV1PairTraceErrorV1 → AdmissionError
  | .Statement a => .Statement (paymentToShared a)
  | .PairLeaf a => .PairLeaf a
  | .Tree a => .Tree (treeToShared a)
  | .Shape  => .Shape 
  | .WrongVariant  => .WrongVariant 
  | .RuntimeBinding  => .RuntimeBinding 
  | .NullifierAlreadySpent  => .NullifierAlreadySpent 
  | .WitnessDigest  => .WitnessDigest 
  | .ValueOutOfRange  => .ValueOutOfRange 
  | .Conservation  => .Conservation 
  | .HashSchedule  => .HashSchedule 
  | .SelectedCommitmentMismatch  => .SelectedCommitmentMismatch 
  | .AnchorMismatch  => .AnchorMismatch 
  | .NullifierMismatch  => .NullifierMismatch 
  | .RecipientCommitmentMismatch  => .RecipientCommitmentMismatch 
  | .ChangeCommitmentMismatch  => .ChangeCommitmentMismatch 
  | .SnapshotBindingMismatch  => .SnapshotBindingMismatch 
  | .BlockMismatch a b c => .BlockMismatch a b c
  | .AuxiliaryMismatch a b => .AuxiliaryMismatch a b
  | .MetadataMismatch  => .MetadataMismatch 
  | .CopyLayout  => .CopyLayout 
  | .CopyImbalance  => .CopyImbalance 

def fromShared : AdmissionError → AspisBuilderAdmissionSource.pool_v1.pair_trace.PoolV1PairTraceErrorV1
  | .Statement a => .Statement (paymentFromShared a)
  | .PairLeaf a => .PairLeaf a
  | .Tree a => .Tree (treeFromShared a)
  | .Shape  => .Shape 
  | .WrongVariant  => .WrongVariant 
  | .RuntimeBinding  => .RuntimeBinding 
  | .NullifierAlreadySpent  => .NullifierAlreadySpent 
  | .WitnessDigest  => .WitnessDigest 
  | .ValueOutOfRange  => .ValueOutOfRange 
  | .Conservation  => .Conservation 
  | .HashSchedule  => .HashSchedule 
  | .SelectedCommitmentMismatch  => .SelectedCommitmentMismatch 
  | .AnchorMismatch  => .AnchorMismatch 
  | .NullifierMismatch  => .NullifierMismatch 
  | .RecipientCommitmentMismatch  => .RecipientCommitmentMismatch 
  | .ChangeCommitmentMismatch  => .ChangeCommitmentMismatch 
  | .SnapshotBindingMismatch  => .SnapshotBindingMismatch 
  | .BlockMismatch a b c => .BlockMismatch a b c
  | .AuxiliaryMismatch a b => .AuxiliaryMismatch a b
  | .MetadataMismatch  => .MetadataMismatch 
  | .CopyLayout  => .CopyLayout 
  | .CopyImbalance  => .CopyImbalance 

theorem from_to (e : AspisBuilderAdmissionSource.pool_v1.pair_trace.PoolV1PairTraceErrorV1) : fromShared (toShared e) = e := by
  cases e <;> simp only [toShared, fromShared, payment_left_inverse, tree_left_inverse]
theorem to_from (e : AdmissionError) : toShared (fromShared e) = e := by
  cases e <;> simp only [toShared, fromShared, payment_right_inverse, tree_right_inverse]

/-- Transport nested Rust errors while retaining Aeneas failure/divergence. -/
def mapRunError {T E F : Type} (f : E → F) :
    Result (core.result.Result T E) → Result (core.result.Result T F)
  | .ok r => .ok (mapCoreError f r)
  | .fail e => .fail e
  | .div => .div

theorem mapRunError_inverse {T E F : Type} (f : E → F) (g : F → E)
    (inv : ∀ e, g (f e) = e) (r : Result (core.result.Result T E)) :
    mapRunError g (mapRunError f r) = r := by
  cases r with
  | ok r => exact congrArg Result.ok (mapCoreError_inverse f g inv r)
  | fail e => rfl
  | div => rfl

theorem mapRunError_success {T E F : Type} (f : E → F)
    (r : Result (core.result.Result T E)) (x : T) :
    mapRunError f r = .ok (.Ok x) ↔ r = .ok (.Ok x) := by
  cases r with
  | ok r => cases r <;> simp only [mapRunError, mapCoreError, Result.ok.injEq,
      core.result.Result.Ok.injEq, reduceCtorEq]
  | fail e => simp only [mapRunError, reduceCtorEq]
  | div => simp only [mapRunError, reduceCtorEq]

/-- Split every privacy result into the eight verifier errors plus all three
prover-only outcomes. No conditional domain or erased error is introduced. -/
def splitProverRun {T : Type}
    (r : Result (core.result.Result T AspisR1ProverCommit.verifier.Error)) :
    Result (core.result.Result T (Sum VerifierShared ProverOnly)) :=
  mapRunError verifierSplit r

theorem prover_run_roundtrip {T : Type}
    (r : Result (core.result.Result T AspisR1ProverCommit.verifier.Error)) :
    mapRunError verifierJoin (splitProverRun r) = r :=
  mapRunError_inverse verifierSplit verifierJoin verifier_join_split r

#print axioms prover_run_roundtrip

open AspisBuilderAdmissionSource
variable (pool domain : Array U8 32#usize) (seq : U64)
  (anchor nullifier : Array aspis_core.field.M31 8#usize)
  (asset : aspis_core.field.M31)
  (input : pool_v1.pair_trace.PoolV1PairInputNoteWitnessV1)
  (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1)

/-- The existing consumer uses only the complete Result success guard. This
boundary exposes canonical NDR payloads without reducing validate_common. -/
def validateCommonShared : Result (core.result.Result Unit AdmissionError) :=
  mapRunError toShared
    (pool_v1.pair_trace.validate_common pool domain seq anchor nullifier asset input context)

theorem validateCommon_roundtrip :
    mapRunError fromShared (validateCommonShared pool domain seq anchor nullifier asset input context) =
      pool_v1.pair_trace.validate_common pool domain seq anchor nullifier asset input context :=
  mapRunError_inverse toShared fromShared from_to _

theorem validateCommon_success :
    validateCommonShared pool domain seq anchor nullifier asset input context = .ok (.Ok ()) ↔
      pool_v1.pair_trace.validate_common pool domain seq anchor nullifier asset input context = .ok (.Ok ()) :=
  mapRunError_success toShared _ ()

#print axioms from_to
#print axioms to_from
#print axioms mapRunError_inverse
#print axioms mapRunError_success
#print axioms validateCommon_roundtrip
#print axioms validateCommon_success
end PV_BR_AdmissionTransport
