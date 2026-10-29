import PV_B3P_CompleteTypes227
import PV_B3P_BytesV3Types226
import R1Z.ProverRwFullExternalFuns
namespace PV_B3P_Carrier227
open Aeneas Aeneas.Std
set_option autoImplicit false
abbrev SQ := PV_B3P_227.aspis_core.field.QM31
abbrev PQ := ProverRwFull.aspis_core.field.QM31

def toQ (q : PQ) : SQ :=
  ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def fromQ (q : SQ) : PQ :=
  ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩

def mapArray {α β : Type} {n : Usize} (f : α → β) (xs : Array α n) : Array β n :=
  ⟨xs.val.map f,by simp only [List.length_map,xs.property]⟩

theorem q_roundtrip (q : PQ) : fromQ (toQ q)=q := by
  cases q with | mk c0 c1 => cases c0; cases c1; rfl

theorem q_reverse (q : SQ) : toQ (fromQ q)=q := by
  cases q with | mk c0 c1 => cases c0; cases c1; rfl

theorem map_roundtrip {α β : Type} {n : Usize} (f : α → β) (g : β → α)
    (h : ∀ a,g (f a)=a) (xs : Array α n) : mapArray g (mapArray f xs)=xs := by
  apply Subtype.ext
  simp only [mapArray,List.map_map,Function.comp_def,h,List.map_id_fun]

theorem q_array_roundtrip {n : Usize} (xs : Array PQ n) :
    mapArray fromQ (mapArray toQ xs)=xs := map_roundtrip toQ fromQ q_roundtrip xs

theorem q_array_reverse {n : Usize} (xs : Array SQ n) :
    mapArray toQ (mapArray fromQ xs)=xs := map_roundtrip fromQ toQ q_reverse xs

@[reducible] def Types (base : ProverRwFull.ExternalTypes) : ProverRwFull.ExternalTypes :=
  {base with
    op6 := PV_B3P_227.aspis_core.state_only_prefix.r0.Error
    op20 := PV_B3P_227.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1
    op21 := PV_B3P_226V3.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1
    op22 := PV_B3P_226V3.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1}

def snapshot (p : ProverRwFull.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) :
    PV_B3P_227.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 :=
  ⟨p.pool,p.deployment_domain,p.sequence,p.next_pair_index,p.current_root,p.frontier⟩

def semantic (base : ProverRwFull.ExternalTypes)
    (p : @ProverRwFull.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public (Types base)) :
    PV_B3P_227.reference_terminal.SemanticPublic :=
  letI : ProverRwFull.ExternalTypes := Types base
  match p with
  | .Transfer pub t =>
    ⟨.PrivateTransfer,pub.pool,pub.deployment_domain,pub.anchor_root,pub.nullifier,
      pub.asset_id,some pub.recipient_commitment,pub.change_commitment,none,
      ⟨snapshot t.live_snapshot,t.candidate_afterstate⟩⟩
  | .Withdrawal pub t =>
    ⟨.Withdrawal,pub.pool,pub.deployment_domain,pub.anchor_root,pub.nullifier,
      pub.asset_id,none,pub.change_commitment,some pub.amount,
      ⟨snapshot t.live_snapshot,t.candidate_afterstate⟩⟩

def challenges (c : ProverRwFull.aspis_core.state_only_prefix.r0.Challenges) :
    PV_B3P_227.aspis_core.state_only_prefix.r0.Challenges :=
  ⟨toQ c.lambda,toQ c.chi,toQ c.theta,mapArray toQ c.zc,toQ c.mu,toQ c.eta⟩

def unChallenges (c : PV_B3P_227.aspis_core.state_only_prefix.r0.Challenges) :
    ProverRwFull.aspis_core.state_only_prefix.r0.Challenges :=
  ⟨fromQ c.lambda,fromQ c.chi,fromQ c.theta,mapArray fromQ c.zc,fromQ c.mu,fromQ c.eta⟩

theorem challenges_roundtrip (c : ProverRwFull.aspis_core.state_only_prefix.r0.Challenges) :
    unChallenges (challenges c)=c := by
  cases c
  simp only [challenges,unChallenges,q_roundtrip,q_array_roundtrip]

theorem challenges_reverse (c : PV_B3P_227.aspis_core.state_only_prefix.r0.Challenges) :
    challenges (unChallenges c)=c := by
  cases c
  simp only [challenges,unChallenges,q_reverse,q_array_reverse]

#print axioms q_roundtrip
#print axioms q_reverse
#print axioms map_roundtrip
#print axioms q_array_roundtrip
#print axioms q_array_reverse
#print axioms challenges_roundtrip
#print axioms challenges_reverse
end PV_B3P_Carrier227
