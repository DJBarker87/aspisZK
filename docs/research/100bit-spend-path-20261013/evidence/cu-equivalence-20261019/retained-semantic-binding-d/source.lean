import CuSavingsRetainedCompositionTx1Source
import CuSavingsRetainedSemanticFinish
import CuSavingsLibraConcrete
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedSemanticBinding
open Aeneas Aeneas.Std Result
namespace P
abbrev D := AspisR1RhoPowerTail.aspis_core.Digest32
abbrev Public := AspisR1RhoPowerTail.pool_v1.pair_forest_semantic_terminal.r0.Public
abbrev Verified := AspisR1RhoPowerTail.r1_semantic.Verified
abbrev K := AspisR1RhoPowerTail.aspis_core.field.QM31
abbrev Phase := AspisR1RhoPowerTail.verifier.Phase
abbrev Error := AspisR1RhoPowerTail.r1_wire.Error
end P
namespace Q
abbrev D := AspisR1PublicPreparation.aspis_core.Digest32
abbrev Public := AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public
abbrev Verified := AspisR1PublicPreparation.r1_semantic.Verified
abbrev K := AspisR1PublicPreparation.aspis_core.field.QM31
abbrev Phase := AspisR1PublicPreparation.verifier.Phase
abbrev Error := AspisR1PublicPreparation.r1_wire.Error
end Q
def digest {H : Type} (d : P.D H) : Q.D H := ⟨d.coremarkerCopyInst,d.digest⟩
def array {A B : Type} {N : Usize} (f : A→B) (xs : Array A N) : Array B N :=
  ⟨xs.val.map f,by simp only [List.length_map,xs.property]⟩
def fromK (x : Q.K) : P.K := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def libraK (x : P.K) : CuSavingsLibraConcrete.L.K := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def afterstate (x : AspisR1CuGamma.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : AspisR1PublicPreparation.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 :=
  {next_pair_index:=x.next_pair_index, next_root:=x.next_root, next_frontier:=x.next_frontier}
def snapshot (x : AspisR1CuGamma.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 :=
  {pool:=x.pool, deployment_domain:=x.deployment_domain, sequence:=x.sequence, next_pair_index:=x.next_pair_index, current_root:=x.current_root, frontier:=x.frontier}
def late (x : AspisR1CuGamma.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 :=
  {live_snapshot:=snapshot (x.live_snapshot), candidate_afterstate:=afterstate (x.candidate_afterstate)}
def transfer (x : AspisR1CuGamma.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 :=
  {pool:=x.pool, deployment_domain:=x.deployment_domain, anchor_sequence:=x.anchor_sequence, anchor_root:=x.anchor_root, nullifier:=x.nullifier, asset_id:=x.asset_id, recipient_commitment:=x.recipient_commitment, change_commitment:=x.change_commitment}
def withdrawal (x : AspisR1CuGamma.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 :=
  {pool:=x.pool, deployment_domain:=x.deployment_domain, anchor_sequence:=x.anchor_sequence, anchor_root:=x.anchor_root, nullifier:=x.nullifier, asset_id:=x.asset_id, amount:=x.amount, destination_token_account:=x.destination_token_account, change_commitment:=x.change_commitment}
def toPublic : P.Public→Q.Public
  | .Transfer pay state => .Transfer (transfer pay) (late state)
  | .Withdrawal pay state => .Withdrawal (withdrawal pay) (late state)
def phase : Q.Phase→P.Phase
  | .Parsed => .Parsed
  | .Semantic => .Semantic
  | .SemanticPart i => .SemanticPart i
  | .Prepare => .Prepare
  | .CheckpointRead => .CheckpointRead
  | .Merkle i => .Merkle i
  | .Query i => .Query i
  | .QueryPart i j => .QueryPart i j
  | .CheckpointWrite => .CheckpointWrite
  | .Relation => .Relation
  | .Final => .Final
def error : Q.Error→P.Error
  | .Allocation => .Allocation
  | .RowOrder i j => .RowOrder i j
  | .InvalidRow => .InvalidRow
  | .Tag i => .Tag i
  | .Length i => .Length i
  | .NonCanonical i j => .NonCanonical i j
  | .Boundary i => .Boundary i
  | .Terminal => .Terminal
  | .EqualCirclePoints => .EqualCirclePoints
  | .TrailingBytes => .TrailingBytes
  | .Public => .Public
def verified {H : Type} (x : Q.Verified H) : P.Verified H :=
  {roots:=x.roots,
   challenges := ⟨fromK x.challenges.lambda, fromK x.challenges.chi,
     fromK x.challenges.theta, array fromK x.challenges.zc,
     fromK x.challenges.mu, fromK x.challenges.eta⟩,
   alpha:=array fromK x.alpha,claims:=array (array fromK) x.claims,
   extra:=array fromK x.extra,before_z1:=array fromK x.before_z1,
   state_before_z0:=x.state_before_z0,
   z:=array (fun z=>{x:=fromK z.x,y:=fromK z.y}) x.z,
   transcript:={state:=x.transcript.state,hash:=x.transcript.hash,next_row:=x.transcript.next_row}}
def verify (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) {H : Type}
    (d : P.D H) (pub : P.Public) (bytes : Slice U8) (hash : H)
    (obs : Option (P.Phase→Result Unit)) : Result (core.result.Result (P.Verified H) P.Error) := do
  let out ← AspisR1PublicPreparation.VerifyPrefix.verify
    (AspisR1PublicPreparation.FinishModel.finish R B) (digest d) (toPublic pub) bytes hash
    (obs.map (fun mark=>fun p=>mark (phase p)))
  .ok (match out with | .Ok value=>.Ok (verified value) | .Err e=>.Err (error e))
@[reducible] def binding (common : AspisR1RhoPowerTail.RetainedPrefix)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) : AspisR1RhoPowerTail.RetainedPrefix :=
  {common with verifyObserved:=verify R B}
#print axioms verify
#print axioms binding
end AspisR1.CuSavingsRetainedSemanticBinding
