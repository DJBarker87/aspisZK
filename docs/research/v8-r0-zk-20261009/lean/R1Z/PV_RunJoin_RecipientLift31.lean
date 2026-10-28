import R1Z.PV_RunJoin_DigestIdentity30
import R1Z.PV_Src_Forest_AuxContent
import R1Z.BuilderFieldNormalization
import R1Z.BuilderSemanticBridge
import R1Z.PV_Src_CompilerTactic
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RecipientLift31
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.BuilderModel
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
open PV_Src_Forest_PrimitiveArguments
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

theorem recipient_lift (r : CopyRecords) (pub : R0P.Public K)
    (hw : WitnessOk (wordWitness r.w)) (hp : PubCorr (wordPublic r.p) pub)
    (hv : pub.variant = .privateTransfer)
    (d : Array U32 8#usize) (hd : CopyRecords.recipient r = ok d) :
    DigestLift d (recipientDigest pub (toModel (wordWitness r.w))) := by
  unfold CopyRecords.recipient at hd
  pv_peel hd with raw hr
  rw [PV_RunJoin_DigestIdentity30.digest] at hd
  cases Result.ok.inj hd
  rw [PV_Src_Forest_AuxContent.recipient_digest] at hr
  have hs := chunks_sabs (wordWitness r.w) (wordPublic r.p) pub hp hw
  obtain ⟨d',he,hl,_⟩ := noteDigest_lift pub (toModel (wordWitness r.w))
    (chunksOf (wordWitness r.w) (wordPublic r.p)) hs ⟨29,by decide⟩
    (by change ¬ NodeKind 29; unfold NodeKind; omega)
    (zk_tr pub 29 hv)
  change noteDigestR (chunksOf (wordWitness r.w) (wordPublic r.p)) 29 = ok d at hr
  rw [hr] at he
  cases Result.ok.inj he
  exact hl
#print axioms recipient_lift

theorem recipient_eq (r : CopyRecords) (pub : R0P.Public K)
    (hw : WitnessOk (wordWitness r.w)) (hp : PubCorr (wordPublic r.p) pub)
    (hv : pub.variant = .privateTransfer)
    (d : Array U32 8#usize) (hd : CopyRecords.recipient r = ok d)
    (hpub : pub.recipient=some (digK d)) :
    pub.recipient = some (AspisR1.SpendRelation.recipientCommitment pub
      (BuilderCanonical.liftWitness (BuilderRecordCanonical.witness (wordWitness r.w)))) := by
  have hl := recipient_lift r pub hw hp hv d hd
  have he : digK (K := K) d = recipientDigest pub (toModel (wordWitness r.w)) := funext hl
  rw [← BuilderFieldNormalization.decoded_witness,BuilderSemanticBridge.recipientDigest_eq _ _ hv] at he
  exact hpub.trans (congrArg some he)
#print axioms recipient_eq
end R1Z.PV_RunJoin_RecipientLift31
