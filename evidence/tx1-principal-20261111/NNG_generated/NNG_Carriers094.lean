import NMT_tx1.Funs
import LIB_Instances
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Carriers094
open Aeneas Aeneas.Std

def arr {A B : Type} {n : Usize} (f : A → B) (x : Array A n) : Array B n :=
 ⟨x.val.map f, by simpa using x.property⟩
def vec {A B : Type} (f : A → B) (x : alloc.vec.Vec A) : alloc.vec.Vec B :=
 ⟨x.val.map f, by simpa using x.property⟩
theorem list_inverse {A B : Type} (f : A → B) (g : B → A)
 (inverse : ∀ x,g (f x)=x) (xs : List A) : (xs.map f).map g=xs := by
 induction xs with
 | nil => rfl
 | cons x xs ih => simp only [List.map_cons,inverse,ih]
#print axioms list_inverse
@[simp] theorem arr_inverse {A B : Type} {n : Usize} (f : A → B) (g : B → A)
 (inverse : ∀ x,g (f x)=x) (xs : Array A n) : arr g (arr f xs)=xs := by
 cases xs
 simp only [arr, list_inverse f g inverse]
@[simp] theorem vec_inverse {A B : Type} (f : A → B) (g : B → A)
 (inverse : ∀ x,g (f x)=x) (xs : alloc.vec.Vec A) : vec g (vec f xs)=xs := by
 cases xs
 simp only [vec, list_inverse f g inverse]
#print axioms arr_inverse
#print axioms vec_inverse
end AspisR1.NNG_Carriers094

namespace AspisR1.NNG_Carriers094
open Aeneas Aeneas.Std
def toT0 (x : NMT_tx1.aspis_core.field.CM31) : AspisR1PublicPreparation.aspis_core.field.CM31 :=
 ⟨x.a,x.b⟩
def fromT0 (x : AspisR1PublicPreparation.aspis_core.field.CM31) : NMT_tx1.aspis_core.field.CM31 :=
 ⟨x.a,x.b⟩
@[simp] theorem toT0_inverse (x : NMT_tx1.aspis_core.field.CM31) : fromT0 (toT0 x)=x := by
 cases x <;> simp [toT0,fromT0]
#print axioms toT0_inverse
@[simp] theorem fromT0_inverse (x : AspisR1PublicPreparation.aspis_core.field.CM31) : toT0 (fromT0 x)=x := by
 cases x <;> simp [fromT0,toT0]
#print axioms fromT0_inverse
end AspisR1.NNG_Carriers094

namespace AspisR1.NNG_Carriers094
open Aeneas Aeneas.Std
def toT1 (x : NMT_tx1.aspis_core.field.QM31) : AspisR1PublicPreparation.aspis_core.field.QM31 :=
 ⟨toT0 (x.c0),toT0 (x.c1)⟩
def fromT1 (x : AspisR1PublicPreparation.aspis_core.field.QM31) : NMT_tx1.aspis_core.field.QM31 :=
 ⟨fromT0 (x.c0),fromT0 (x.c1)⟩
@[simp] theorem toT1_inverse (x : NMT_tx1.aspis_core.field.QM31) : fromT1 (toT1 x)=x := by
 cases x <;> simp [toT1,fromT1]
#print axioms toT1_inverse
@[simp] theorem fromT1_inverse (x : AspisR1PublicPreparation.aspis_core.field.QM31) : toT1 (fromT1 x)=x := by
 cases x <;> simp [fromT1,toT1]
#print axioms fromT1_inverse
end AspisR1.NNG_Carriers094

namespace AspisR1.NNG_Carriers094
open Aeneas Aeneas.Std
def toT2 (x : NMT_tx1.aspis_core.circle.SecureCirclePoint) : AspisR1PublicPreparation.aspis_core.circle.SecureCirclePoint :=
 ⟨toT1 (x.x),toT1 (x.y)⟩
def fromT2 (x : AspisR1PublicPreparation.aspis_core.circle.SecureCirclePoint) : NMT_tx1.aspis_core.circle.SecureCirclePoint :=
 ⟨fromT1 (x.x),fromT1 (x.y)⟩
@[simp] theorem toT2_inverse (x : NMT_tx1.aspis_core.circle.SecureCirclePoint) : fromT2 (toT2 x)=x := by
 cases x <;> simp [toT2,fromT2]
#print axioms toT2_inverse
@[simp] theorem fromT2_inverse (x : AspisR1PublicPreparation.aspis_core.circle.SecureCirclePoint) : toT2 (fromT2 x)=x := by
 cases x <;> simp [fromT2,toT2]
#print axioms fromT2_inverse
end AspisR1.NNG_Carriers094

namespace AspisR1.NNG_Carriers094
open Aeneas Aeneas.Std
def toT3 (x : NMT_tx1.aspis_core.field.wide_exact.WideExact) : AspisR1PublicPreparation.aspis_core.field.WideExact :=
 ⟨toT1 (x.c0),toT1 (x.c1)⟩
def fromT3 (x : AspisR1PublicPreparation.aspis_core.field.WideExact) : NMT_tx1.aspis_core.field.wide_exact.WideExact :=
 ⟨fromT1 (x.c0),fromT1 (x.c1)⟩
@[simp] theorem toT3_inverse (x : NMT_tx1.aspis_core.field.wide_exact.WideExact) : fromT3 (toT3 x)=x := by
 cases x <;> simp [toT3,fromT3]
#print axioms toT3_inverse
@[simp] theorem fromT3_inverse (x : AspisR1PublicPreparation.aspis_core.field.WideExact) : toT3 (fromT3 x)=x := by
 cases x <;> simp [fromT3,toT3]
#print axioms fromT3_inverse
end AspisR1.NNG_Carriers094

namespace AspisR1.NNG_Carriers094
open Aeneas Aeneas.Std
def toT4 (x : NMT_tx1.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 :=
 ⟨x.pool,x.deployment_domain,x.anchor_sequence,x.anchor_root,x.nullifier,x.asset_id,x.amount,x.destination_token_account,x.change_commitment⟩
def fromT4 (x : AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : NMT_tx1.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 :=
 ⟨x.pool,x.deployment_domain,x.anchor_sequence,x.anchor_root,x.nullifier,x.asset_id,x.amount,x.destination_token_account,x.change_commitment⟩
@[simp] theorem toT4_inverse (x : NMT_tx1.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : fromT4 (toT4 x)=x := by
 cases x <;> simp [toT4,fromT4]
#print axioms toT4_inverse
@[simp] theorem fromT4_inverse (x : AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : toT4 (fromT4 x)=x := by
 cases x <;> simp [fromT4,toT4]
#print axioms fromT4_inverse
end AspisR1.NNG_Carriers094

namespace AspisR1.NNG_Carriers094
open Aeneas Aeneas.Std
def toT5 (x : NMT_tx1.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 :=
 ⟨x.pool,x.deployment_domain,x.anchor_sequence,x.anchor_root,x.nullifier,x.asset_id,x.recipient_commitment,x.change_commitment⟩
def fromT5 (x : AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : NMT_tx1.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 :=
 ⟨x.pool,x.deployment_domain,x.anchor_sequence,x.anchor_root,x.nullifier,x.asset_id,x.recipient_commitment,x.change_commitment⟩
@[simp] theorem toT5_inverse (x : NMT_tx1.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : fromT5 (toT5 x)=x := by
 cases x <;> simp [toT5,fromT5]
#print axioms toT5_inverse
@[simp] theorem fromT5_inverse (x : AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : toT5 (fromT5 x)=x := by
 cases x <;> simp [fromT5,toT5]
#print axioms fromT5_inverse
end AspisR1.NNG_Carriers094

namespace AspisR1.NNG_Carriers094
open Aeneas Aeneas.Std
def toT6 (x : NMT_tx1.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 :=
 ⟨x.pool,x.deployment_domain,x.sequence,x.next_pair_index,x.current_root,x.frontier⟩
def fromT6 (x : AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : NMT_tx1.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 :=
 ⟨x.pool,x.deployment_domain,x.sequence,x.next_pair_index,x.current_root,x.frontier⟩
@[simp] theorem toT6_inverse (x : NMT_tx1.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : fromT6 (toT6 x)=x := by
 cases x <;> simp [toT6,fromT6]
#print axioms toT6_inverse
@[simp] theorem fromT6_inverse (x : AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : toT6 (fromT6 x)=x := by
 cases x <;> simp [fromT6,toT6]
#print axioms fromT6_inverse
end AspisR1.NNG_Carriers094

namespace AspisR1.NNG_Carriers094
open Aeneas Aeneas.Std
def toT7 (x : NMT_tx1.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : AspisR1PublicPreparation.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 :=
 ⟨x.next_pair_index,x.next_root,x.next_frontier⟩
def fromT7 (x : AspisR1PublicPreparation.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : NMT_tx1.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 :=
 ⟨x.next_pair_index,x.next_root,x.next_frontier⟩
@[simp] theorem toT7_inverse (x : NMT_tx1.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : fromT7 (toT7 x)=x := by
 cases x <;> simp [toT7,fromT7]
#print axioms toT7_inverse
@[simp] theorem fromT7_inverse (x : AspisR1PublicPreparation.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : toT7 (fromT7 x)=x := by
 cases x <;> simp [fromT7,toT7]
#print axioms fromT7_inverse
end AspisR1.NNG_Carriers094

namespace AspisR1.NNG_Carriers094
open Aeneas Aeneas.Std
def toT8 (x : NMT_tx1.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 :=
 ⟨toT6 (x.live_snapshot),toT7 (x.candidate_afterstate)⟩
def fromT8 (x : AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : NMT_tx1.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 :=
 ⟨fromT6 (x.live_snapshot),fromT7 (x.candidate_afterstate)⟩
@[simp] theorem toT8_inverse (x : NMT_tx1.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : fromT8 (toT8 x)=x := by
 cases x <;> simp [toT8,fromT8]
#print axioms toT8_inverse
@[simp] theorem fromT8_inverse (x : AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : toT8 (fromT8 x)=x := by
 cases x <;> simp [fromT8,toT8]
#print axioms fromT8_inverse
end AspisR1.NNG_Carriers094

namespace AspisR1.NNG_Carriers094
open Aeneas Aeneas.Std
def toT9 : NMT_tx1.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public → AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public
 | .Transfer x0 x1 => .Transfer (toT5 (x0)) (toT8 (x1))
 | .Withdrawal x0 x1 => .Withdrawal (toT4 (x0)) (toT8 (x1))
def fromT9 : AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public → NMT_tx1.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
 | .Transfer x0 x1 => .Transfer (fromT5 (x0)) (fromT8 (x1))
 | .Withdrawal x0 x1 => .Withdrawal (fromT4 (x0)) (fromT8 (x1))
@[simp] theorem toT9_inverse (x : NMT_tx1.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) : fromT9 (toT9 x)=x := by
 cases x <;> simp [toT9,fromT9]
#print axioms toT9_inverse
@[simp] theorem fromT9_inverse (x : AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public) : toT9 (fromT9 x)=x := by
 cases x <;> simp [fromT9,toT9]
#print axioms fromT9_inverse
end AspisR1.NNG_Carriers094

namespace AspisR1.NNG_Carriers094
open Aeneas Aeneas.Std
def toT10 : NMT_tx1.verifier.Error → AspisR1PublicPreparation.verifier.Error
 | .Parse => .Parse
 | .Semantic => .Semantic
 | .Transcript => .Transcript
 | .Relation => .Relation
 | .Merkle => .Merkle
 | .Query => .Query
 | .Checkpoint => .Checkpoint
 | .Allocation => .Allocation
def fromT10 : AspisR1PublicPreparation.verifier.Error → NMT_tx1.verifier.Error
 | .Parse => .Parse
 | .Semantic => .Semantic
 | .Transcript => .Transcript
 | .Relation => .Relation
 | .Merkle => .Merkle
 | .Query => .Query
 | .Checkpoint => .Checkpoint
 | .Allocation => .Allocation
@[simp] theorem toT10_inverse (x : NMT_tx1.verifier.Error) : fromT10 (toT10 x)=x := by
 cases x <;> simp [toT10,fromT10]
#print axioms toT10_inverse
@[simp] theorem fromT10_inverse (x : AspisR1PublicPreparation.verifier.Error) : toT10 (fromT10 x)=x := by
 cases x <;> simp [fromT10,toT10]
#print axioms fromT10_inverse
end AspisR1.NNG_Carriers094

namespace AspisR1.NNG_Carriers094
open Aeneas Aeneas.Std
def toT11 : NMT_tx1.transport.Variant → AspisR1PublicPreparation.transport.Variant
 | .S1 => .S1
 | .S2 => .S2
 | .D => .D
def fromT11 : AspisR1PublicPreparation.transport.Variant → NMT_tx1.transport.Variant
 | .S1 => .S1
 | .S2 => .S2
 | .D => .D
@[simp] theorem toT11_inverse (x : NMT_tx1.transport.Variant) : fromT11 (toT11 x)=x := by
 cases x <;> simp [toT11,fromT11]
#print axioms toT11_inverse
@[simp] theorem fromT11_inverse (x : AspisR1PublicPreparation.transport.Variant) : toT11 (fromT11 x)=x := by
 cases x <;> simp [fromT11,toT11]
#print axioms fromT11_inverse
end AspisR1.NNG_Carriers094

namespace AspisR1.NNG_Carriers094
open Aeneas Aeneas.Std
def toT12 (x : NMT_tx1.verifier.Prepared) : AspisR1PublicPreparation.verifier.Prepared :=
 ⟨toT11 (x.variant),x.roots,toT3 (x.gamma),toT3 (x.kappa),arr (fun z => toT3 (z)) (x.alpha),toT1 (x.rho),x.queries,arr (fun z => toT1 (z)) (x.semantic_alpha),arr (fun z => toT2 (z)) (x.z),toT3 (x.claim),x.state⟩
def fromT12 (x : AspisR1PublicPreparation.verifier.Prepared) : NMT_tx1.verifier.Prepared :=
 ⟨fromT11 (x.variant),x.roots,fromT3 (x.gamma),fromT3 (x.kappa),arr (fun z => fromT3 (z)) (x.alpha),fromT1 (x.rho),x.queries,arr (fun z => fromT1 (z)) (x.semantic_alpha),arr (fun z => fromT2 (z)) (x.z),fromT3 (x.claim),x.state⟩
@[simp] theorem toT12_inverse (x : NMT_tx1.verifier.Prepared) : fromT12 (toT12 x)=x := by
 cases x <;> simp [toT12,fromT12]
#print axioms toT12_inverse
@[simp] theorem fromT12_inverse (x : AspisR1PublicPreparation.verifier.Prepared) : toT12 (fromT12 x)=x := by
 cases x <;> simp [fromT12,toT12]
#print axioms fromT12_inverse
end AspisR1.NNG_Carriers094

namespace AspisR1.NNG_Carriers094
open Aeneas Aeneas.Std
def toT13 (x : NMT_tx1.verifier.BatchedWeights) : AspisR1Stage2.verifier.BatchedWeights :=
 ⟨x.«raw»,x.terms⟩
def fromT13 (x : AspisR1Stage2.verifier.BatchedWeights) : NMT_tx1.verifier.BatchedWeights :=
 ⟨x.«raw»,x.terms⟩
@[simp] theorem toT13_inverse (x : NMT_tx1.verifier.BatchedWeights) : fromT13 (toT13 x)=x := by
 cases x <;> simp [toT13,fromT13]
#print axioms toT13_inverse
@[simp] theorem fromT13_inverse (x : AspisR1Stage2.verifier.BatchedWeights) : toT13 (fromT13 x)=x := by
 cases x <;> simp [fromT13,toT13]
#print axioms fromT13_inverse
end AspisR1.NNG_Carriers094

namespace AspisR1.NNG_Carriers094
open Aeneas Aeneas.Std
def toT14 (x : NMT_tx1.verifier.QueryGeometry) : AspisR1Stage2.verifier.QueryGeometry :=
 ⟨x.start,x.inverses,x.line_z⟩
def fromT14 (x : AspisR1Stage2.verifier.QueryGeometry) : NMT_tx1.verifier.QueryGeometry :=
 ⟨x.start,x.inverses,x.line_z⟩
@[simp] theorem toT14_inverse (x : NMT_tx1.verifier.QueryGeometry) : fromT14 (toT14 x)=x := by
 cases x <;> simp [toT14,fromT14]
#print axioms toT14_inverse
@[simp] theorem fromT14_inverse (x : AspisR1Stage2.verifier.QueryGeometry) : toT14 (fromT14 x)=x := by
 cases x <;> simp [fromT14,toT14]
#print axioms fromT14_inverse
end AspisR1.NNG_Carriers094

namespace AspisR1.NNG_Carriers094
open Aeneas Aeneas.Std
def toT15 (x : NMT_tx1.verifier.Accumulator) : AspisR1PublicPreparation.verifier.Accumulator :=
 ⟨vec (fun z => toT1 (z)) (x.weights),toT3 (x.rhs),toT1 (x.power),x.next⟩
def fromT15 (x : AspisR1PublicPreparation.verifier.Accumulator) : NMT_tx1.verifier.Accumulator :=
 ⟨vec (fun z => fromT1 (z)) (x.weights),fromT3 (x.rhs),fromT1 (x.power),x.next⟩
@[simp] theorem toT15_inverse (x : NMT_tx1.verifier.Accumulator) : fromT15 (toT15 x)=x := by
 cases x <;> simp [toT15,fromT15]
#print axioms toT15_inverse
@[simp] theorem fromT15_inverse (x : AspisR1PublicPreparation.verifier.Accumulator) : toT15 (fromT15 x)=x := by
 cases x <;> simp [fromT15,toT15]
#print axioms fromT15_inverse
end AspisR1.NNG_Carriers094

