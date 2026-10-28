import R1Z.PV_RunJoin_RecordInputLift31
import R1Z.PV_Src_Forest_AppendArguments
import R1Z.BuilderSpendRelation
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RecordAppendLift31
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.BuilderModel
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
open PV_Src_Forest_PrimitiveArguments
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

theorem prefix (r : CopyRecords) (pub : R0P.Public K)
    (hw : WitnessOk (wordWitness r.w)) (hp : PubCorr (wordPublic r.p) pub)
    (n : Usize) (hn : n.val ≤ 20)
    (d : Array U32 8#usize) (hd : app_cur_r r.w r.p n = ok d) :
    digK d = AspisR1.AppendPath.pathPrefix pub (outPair pub (toModel (wordWitness r.w))) n.val := by
  rw [PV_Src_Forest_AppendArguments.append r.w r.p n hn] at hd
  obtain ⟨out,ho,hm,_⟩ := appCur_lift (wordWitness r.w) (wordPublic r.p) pub hp hw n.val hn
  rw [hd] at ho
  cases Result.ok.inj ho
  have he := funext hm
  rw [BuilderSpendRelation.appCur_eq pub (toModel (wordWitness r.w))] at he
  exact he
#print axioms prefix

theorem root (r : CopyRecords) (pub : R0P.Public K)
    (hw : WitnessOk (wordWitness r.w)) (hp : PubCorr (wordPublic r.p) pub)
    (d : Array U32 8#usize) (hd : CopyRecords.append_root r = ok d) :
    digK d = AspisR1.AppendPath.pathPrefix pub (outPair pub (toModel (wordWitness r.w))) 20 := by
  unfold CopyRecords.append_root at hd
  pv_peel hd with raw hr
  rw [PV_RunJoin_DigestIdentity30.digest] at hd
  cases Result.ok.inj hd
  exact prefix r pub hw hp 20#usize (by decide) _ hr
#print axioms root
end R1Z.PV_RunJoin_RecordAppendLift31
