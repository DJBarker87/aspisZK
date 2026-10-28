import PV_B3P_BytesV3Types226
import R1Z.ProverRwFullExternalFuns
namespace PV_B3P_PublicCarrier226V3
open Aeneas Aeneas.Std ProverRwFull
set_option autoImplicit false

@[reducible] def Types (base : ExternalTypes) : ExternalTypes :=
  {base with
    op6 := PV_B3P_226V3.aspis_core.state_only_prefix.r0.Error
    op20 := PV_B3P_226V3.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1
    op21 := PV_B3P_226V3.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1
    op22 := PV_B3P_226V3.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1}

def snapshot (p : ProverRwFull.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) :
    PV_B3P_226V3.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 :=
  ⟨p.pool,p.deployment_domain,p.sequence,p.next_pair_index,p.current_root,p.frontier⟩

def unSnapshot (p : PV_B3P_226V3.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) :
    ProverRwFull.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 :=
  ⟨p.pool,p.deployment_domain,p.sequence,p.next_pair_index,p.current_root,p.frontier⟩

def toSource (base : ExternalTypes)
    (p : @ProverRwFull.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public (Types base)) :
    PV_B3P_226V3.reference226.Source :=
  match p with
  | .Transfer pub t => .Transfer pub ⟨snapshot t.live_snapshot,t.candidate_afterstate⟩
  | .Withdrawal pub t => .Withdrawal pub ⟨snapshot t.live_snapshot,t.candidate_afterstate⟩

def fromSource (base : ExternalTypes) (p : PV_B3P_226V3.reference226.Source) :
    @ProverRwFull.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public (Types base) :=
  match p with
  | .Transfer pub t => .Transfer pub ⟨unSnapshot t.live_snapshot,t.candidate_afterstate⟩
  | .Withdrawal pub t => .Withdrawal pub ⟨unSnapshot t.live_snapshot,t.candidate_afterstate⟩

theorem snapshot_roundtrip (p : ProverRwFull.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) :
    unSnapshot (snapshot p) = p := by cases p; rfl

theorem snapshot_reverse (p : PV_B3P_226V3.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) :
    snapshot (unSnapshot p) = p := by cases p; rfl

theorem roundtrip (base : ExternalTypes)
    (p : @ProverRwFull.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public (Types base)) :
    fromSource base (toSource base p) = p := by
  cases p with
  | Transfer pub t => cases t with | mk live after => cases live; rfl
  | Withdrawal pub t => cases t with | mk live after => cases live; rfl

theorem reverse_roundtrip (base : ExternalTypes) (p : PV_B3P_226V3.reference226.Source) :
    toSource base (fromSource base p) = p := by
  cases p with
  | Transfer pub t => cases t with | mk live after => cases live; rfl
  | Withdrawal pub t => cases t with | mk live after => cases live; rfl

#print axioms snapshot_roundtrip
#print axioms snapshot_reverse
#print axioms roundtrip
#print axioms reverse_roundtrip
theorem preserved_type0 (base : ExternalTypes) :
    @ExternalTypes.op0 (Types base) = @ExternalTypes.op0 base := rfl
#print axioms preserved_type0
theorem preserved_type1 (base : ExternalTypes) :
    @ExternalTypes.op1 (Types base) = @ExternalTypes.op1 base := rfl
#print axioms preserved_type1
theorem preserved_type2 (base : ExternalTypes) :
    @ExternalTypes.op2 (Types base) = @ExternalTypes.op2 base := rfl
#print axioms preserved_type2
theorem preserved_type3 (base : ExternalTypes) :
    @ExternalTypes.op3 (Types base) = @ExternalTypes.op3 base := rfl
#print axioms preserved_type3
theorem preserved_type4 (base : ExternalTypes) :
    @ExternalTypes.op4 (Types base) = @ExternalTypes.op4 base := rfl
#print axioms preserved_type4
theorem preserved_type5 (base : ExternalTypes) :
    @ExternalTypes.op5 (Types base) = @ExternalTypes.op5 base := rfl
#print axioms preserved_type5
theorem preserved_type7 (base : ExternalTypes) :
    @ExternalTypes.op7 (Types base) = @ExternalTypes.op7 base := rfl
#print axioms preserved_type7
theorem preserved_type8 (base : ExternalTypes) :
    @ExternalTypes.op8 (Types base) = @ExternalTypes.op8 base := rfl
#print axioms preserved_type8
theorem preserved_type9 (base : ExternalTypes) :
    @ExternalTypes.op9 (Types base) = @ExternalTypes.op9 base := rfl
#print axioms preserved_type9
theorem preserved_type10 (base : ExternalTypes) :
    @ExternalTypes.op10 (Types base) = @ExternalTypes.op10 base := rfl
#print axioms preserved_type10
theorem preserved_type11 (base : ExternalTypes) :
    @ExternalTypes.op11 (Types base) = @ExternalTypes.op11 base := rfl
#print axioms preserved_type11
theorem preserved_type12 (base : ExternalTypes) :
    @ExternalTypes.op12 (Types base) = @ExternalTypes.op12 base := rfl
#print axioms preserved_type12
theorem preserved_type13 (base : ExternalTypes) :
    @ExternalTypes.op13 (Types base) = @ExternalTypes.op13 base := rfl
#print axioms preserved_type13
theorem preserved_type14 (base : ExternalTypes) :
    @ExternalTypes.op14 (Types base) = @ExternalTypes.op14 base := rfl
#print axioms preserved_type14
theorem preserved_type15 (base : ExternalTypes) :
    @ExternalTypes.op15 (Types base) = @ExternalTypes.op15 base := rfl
#print axioms preserved_type15
theorem preserved_type16 (base : ExternalTypes) :
    @ExternalTypes.op16 (Types base) = @ExternalTypes.op16 base := rfl
#print axioms preserved_type16
theorem preserved_type17 (base : ExternalTypes) :
    @ExternalTypes.op17 (Types base) = @ExternalTypes.op17 base := rfl
#print axioms preserved_type17
theorem preserved_type18 (base : ExternalTypes) :
    @ExternalTypes.op18 (Types base) = @ExternalTypes.op18 base := rfl
#print axioms preserved_type18
theorem preserved_type19 (base : ExternalTypes) :
    @ExternalTypes.op19 (Types base) = @ExternalTypes.op19 base := rfl
#print axioms preserved_type19
theorem preserved_type23 (base : ExternalTypes) :
    @ExternalTypes.op23 (Types base) = @ExternalTypes.op23 base := rfl
#print axioms preserved_type23
theorem preserved_type24 (base : ExternalTypes) :
    @ExternalTypes.op24 (Types base) = @ExternalTypes.op24 base := rfl
#print axioms preserved_type24
theorem preserved_type25 (base : ExternalTypes) :
    @ExternalTypes.op25 (Types base) = @ExternalTypes.op25 base := rfl
#print axioms preserved_type25
theorem preserved_type26 (base : ExternalTypes) :
    @ExternalTypes.op26 (Types base) = @ExternalTypes.op26 base := rfl
#print axioms preserved_type26
theorem preserved_type27 (base : ExternalTypes) :
    @ExternalTypes.op27 (Types base) = @ExternalTypes.op27 base := rfl
#print axioms preserved_type27
end PV_B3P_PublicCarrier226V3
