import R1Z.PV_RunJoin_CanonicalWordEq31
import R1Z.PV_RunJoin_SnapshotUnique31
import R1Z.PV_RunJoin_SemanticAppendRoot31
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SnapshotAgreement31
open Aeneas Aeneas.Std Result R0Z.WriterRefine R1J.SpendWitnessMap PV_Src_NativeInput
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_RunJoin_SemanticChange30
local instance : ExternalLinear := PV_RunJoin_ShippedExternal.E_shipped
local instance : Records := PV_RunJoin_UniversalRecords22.shipped
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

theorem field_index (i : Input) (success : run i = ok (.Ok i.compiled)) :
    i.snapshot.next_pair_index.val = (statement (K := K) i).nextPairIndex := by
  have hs := PV_RunJoin_UniversalRecords22.snapshot i success
  cases hreq : i.request <;>
    simp only [statement,publicInput,PV_Src_NativeInput.transition,hreq,
      PV_Src_Public.canonicalPublic,BuilderPublicProjection.transferPublic,
      BuilderPublicProjection.withdrawalPublic,mapPub] <;> rw [hs]
#print axioms field_index

theorem field_frontier (i : Input) (success : run i = ok (.Ok i.compiled)) (j : Fin 20) :
    digK i.snapshot.frontier.val[j.val]! = (statement (K := K) i).snapshotFrontier j := by
  have hs := PV_RunJoin_UniversalRecords22.snapshot i success
  cases hreq : i.request <;> funext lane <;>
    simp only [statement,publicInput,PV_Src_NativeInput.transition,hreq,
      PV_Src_Public.canonicalPublic,BuilderPublicProjection.transferPublic,
      BuilderPublicProjection.withdrawalPublic,mapPub] <;> rw [hs] <;>
    simp only [digK,liftU,map_natCast]
#print axioms field_frontier

/-- The source fixes metadata omitted from the field-level Public: root and
sequence follow from equal index/frontier plus successful preparation. -/
theorem agree (a b : Input) (sa : run a = ok (.Ok a.compiled)) (sb : run b = ok (.Ok b.compiled))
    (fa : ∀ j : Fin 20, Canon8 a.snapshot.frontier.val[j.val]!)
    (fb : ∀ j : Fin 20, Canon8 b.snapshot.frontier.val[j.val]!)
    (same : statement (K := K) a = statement (K := K) b) :
    a.snapshot.next_pair_index = b.snapshot.next_pair_index ∧
    a.snapshot.frontier = b.snapshot.frontier ∧
    a.snapshot.current_root = b.snapshot.current_root ∧ a.snapshot.sequence = b.snapshot.sequence := by
  have hi := congrArg (fun p : R0P.Public K => p.nextPairIndex) same
  have hf := congrArg (fun p : R0P.Public K => p.snapshotFrontier) same
  have index : a.snapshot.next_pair_index = b.snapshot.next_pair_index := UScalar.eq_of_val_eq
    ((field_index a sa).trans (hi.trans (field_index b sb).symm))
  have frontier : a.snapshot.frontier = b.snapshot.frontier := PV_RunJoin_CanonicalWordEq31.frontier (K := K)
    _ _ fa fb (fun j => (field_frontier a sa j).trans ((congrFun hf j).trans (field_frontier b sb j).symm))
  obtain ⟨ra,la,hra,hleafA,hA⟩ := PV_RunJoin_CompilerAppend31.afterstate a.witness
    (outputValue a.request) (recipient a.request) a.change (forestPublic a.request) a.laneAnchor a.snapshot a.compiled sa
  obtain ⟨rb,lb,hrb,hleafB,hB⟩ := PV_RunJoin_CompilerAppend31.afterstate b.witness
    (outputValue b.request) (recipient b.request) b.change (forestPublic b.request) b.laneAnchor b.snapshot b.compiled sb
  have roots := PV_RunJoin_SnapshotUnique31.root a.snapshot b.snapshot ra rb la lb _ _ hA hB index frontier
  have seqA := PV_RunJoin_SnapshotUnique31.sequence ra a.snapshot la _ hA
  have seqB := PV_RunJoin_SnapshotUnique31.sequence rb b.snapshot lb _ hB
  exact ⟨index,frontier,roots,seqA.trans (index.trans seqB.symm)⟩
#print axioms agree

theorem snapshot_ext (a b : pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (hp : a.pool=b.pool) (hd : a.deployment_domain=b.deployment_domain)
    (hs : a.sequence=b.sequence) (hi : a.next_pair_index=b.next_pair_index)
    (hr : a.current_root=b.current_root) (hf : a.frontier=b.frontier) : a=b := by
  rcases a with ⟨pa,da,sa,ia,ra,fa⟩
  rcases b with ⟨pb,db,sb,ib,rb,fb⟩
  dsimp only at hp hd hs hi hr hf
  cases hp
  cases hd
  cases hs
  cases hi
  cases hr
  cases hf
  rfl
#print axioms snapshot_ext

/-- Context-byte agreement stays explicit P work; root/sequence are derived. -/
theorem whole (a b : Input) (sa : run a = ok (.Ok a.compiled)) (sb : run b = ok (.Ok b.compiled))
    (fa : ∀ j : Fin 20, Canon8 a.snapshot.frontier.val[j.val]!)
    (fb : ∀ j : Fin 20, Canon8 b.snapshot.frontier.val[j.val]!)
    (same : statement (K := K) a = statement (K := K) b)
    (pool : a.snapshot.pool=b.snapshot.pool)
    (domain : a.snapshot.deployment_domain=b.snapshot.deployment_domain) : a.snapshot=b.snapshot := by
  have fields := agree a b sa sb fa fb same
  exact snapshot_ext _ _ pool domain fields.2.2.2 fields.1 fields.2.2.1 fields.2.1
#print axioms whole
end R1Z.PV_RunJoin_SnapshotAgreement31
