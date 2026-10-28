import R1Z.PV_RunJoin_DigestIdentity30
import R1Z.PV_Src_Forest_AuxContent
import R1Z.BuilderFieldNormalization
import R1Z.BuilderSemanticBridge
import R1Z.PV_Src_CompilerTactic
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ChangeLift30
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.BuilderModel
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
open PV_Src_Forest_PrimitiveArguments
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

theorem change_lift (r : CopyRecords) (pub : R0P.Public K)
    (hw : WitnessOk (wordWitness r.w)) (hp : PubCorr (wordPublic r.p) pub)
    (d : Array U32 8#usize) (hd : CopyRecords.change r = ok d) :
    DigestLift d (changeDigest pub (toModel (wordWitness r.w))) := by
  unfold CopyRecords.change at hd
  pv_peel hd with raw hr
  rw [PV_RunJoin_DigestIdentity30.digest] at hd
  cases Result.ok.inj hd
  rw [PV_Src_Forest_AuxContent.change_digest] at hr
  have hs := chunks_sabs (wordWitness r.w) (wordPublic r.p) pub hp hw
  obtain ⟨d',he,hl,_⟩ := noteDigest_lift pub (toModel (wordWitness r.w))
    (chunksOf (wordWitness r.w) (wordPublic r.p)) hs ⟨32,by decide⟩
    (by unfold NodeKind; omega) (by unfold ZeroKind; omega)
  change noteDigestR (chunksOf (wordWitness r.w) (wordPublic r.p)) 32 = ok raw at hr
  rw [hr] at he
  cases Result.ok.inj he
  exact hl
#print axioms change_lift

theorem change_eq (r : CopyRecords) (pub : R0P.Public K)
    (hw : WitnessOk (wordWitness r.w)) (hp : PubCorr (wordPublic r.p) pub)
    (d : Array U32 8#usize) (hd : CopyRecords.change r = ok d)
    (hpub : pub.change=digK d) :
    pub.change = AspisR1.SpendRelation.changeCommitment pub
      (BuilderCanonical.liftWitness (BuilderRecordCanonical.witness (wordWitness r.w))) := by
  have hl := change_lift r pub hw hp d hd
  have he : digK (K := K) d = changeDigest pub (toModel (wordWitness r.w)) := funext hl
  rw [← BuilderFieldNormalization.decoded_witness,BuilderSemanticBridge.changeDigest_eq] at he
  exact hpub.trans he
#print axioms change_eq
end R1Z.PV_RunJoin_ChangeLift30
