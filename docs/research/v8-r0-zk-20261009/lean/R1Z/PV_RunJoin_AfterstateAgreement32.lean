import R1Z.PV_RunJoin_OutputAgreement32
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_AfterstateAgreement32
open Aeneas Aeneas.Std Result PV_Src_NativeInput PV_RunJoin_HonestIdentification26
local instance : BuilderForestAdmissionPort.ExternalLinear := PV_RunJoin_ShippedExternal.E_shipped
local instance : BuilderForestAdmissionPort.Records := PV_RunJoin_UniversalRecords22.shipped
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

theorem afterstate (a b : Honest (K := K))
    (same : source_honest.public a=source_honest.public b)
    (pool : a.val.snapshot.pool=b.val.snapshot.pool)
    (domain : a.val.snapshot.deployment_domain=b.val.snapshot.deployment_domain) :
    a.val.compiled.public_statement.candidate_afterstate=b.val.compiled.public_statement.candidate_afterstate := by
  obtain ⟨ra,la,hra,hla,haa⟩ := PV_RunJoin_CompilerAppend31.afterstate a.val.witness
    (outputValue a.val.request) (recipient a.val.request) a.val.change (forestPublic a.val.request)
    a.val.laneAnchor a.val.snapshot a.val.compiled (success a)
  obtain ⟨rb,lb,hrb,hlb,hab⟩ := PV_RunJoin_CompilerAppend31.afterstate b.val.witness
    (outputValue b.val.request) (recipient b.val.request) b.val.change (forestPublic b.val.request)
    b.val.laneAnchor b.val.snapshot b.val.compiled (success b)
  have hleaf := PV_RunJoin_OutputAgreement32.unique a b same ra rb hra hrb la lb hla hlb
  have hs := PV_RunJoin_NativeSnapshotAgreement32.snapshots a b same pool domain
  rw [hs,hleaf] at haa
  exact PV_RunJoin_AppendDeterminism32.unique ra rb b.val.snapshot lb _ _ haa hab
#print axioms afterstate

theorem transition (a b : Honest (K := K))
    (same : source_honest.public a=source_honest.public b)
    (pool : a.val.snapshot.pool=b.val.snapshot.pool)
    (domain : a.val.snapshot.deployment_domain=b.val.snapshot.deployment_domain) :
    a.val.compiled.public_statement=b.val.compiled.public_statement := by
  have hs := PV_RunJoin_NativeSnapshotAgreement32.snapshots a b same pool domain
  have ha := afterstate a b same pool domain
  have sa := PV_RunJoin_UniversalRecords22.snapshot a.val (success a)
  have sb := PV_RunJoin_UniversalRecords22.snapshot b.val (success b)
  have live := sa.trans (hs.trans sb.symm)
  exact congrArg₂ (fun s t =>
    BuilderForestAdmissionPort.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.mk s t) live ha
#print axioms transition
end R1Z.PV_RunJoin_AfterstateAgreement32
