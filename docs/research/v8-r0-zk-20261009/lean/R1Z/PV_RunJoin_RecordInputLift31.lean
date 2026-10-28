import R1Z.PV_RunJoin_ChangeLift30
import R1Z.PV_RunJoin_NullifierLift16
import R1Z.PV_RunJoin_TreeLift16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RecordInputLift31
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.BuilderModel
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
open PV_Src_Forest_PrimitiveArguments
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

theorem input (r : CopyRecords) (pub : R0P.Public K)
    (hw : WitnessOk (wordWitness r.w)) (hp : PubCorr (wordPublic r.p) pub)
    (d : Array U32 8#usize) (hd : CopyRecords.input_leaf r = ok d) :
    digK d = R0P.noteCommitment (R0P.ownerKey (toModel (K := K) (wordWitness r.w)).sk)
      ((toModel (K := K) (wordWitness r.w)).inputValue.val : K) pub.assetId
      (toModel (K := K) (wordWitness r.w)).salt := by
  unfold CopyRecords.input_leaf at hd
  pv_peel hd with raw hr
  rw [PV_RunJoin_DigestIdentity30.digest] at hd
  cases Result.ok.inj hd
  rw [PV_Src_Forest_AuxContent.input_digest] at hr
  obtain ⟨out,ho,hm,_⟩ := PV_RunJoin_LeafLift16.input (wordWitness r.w) (wordPublic r.p) pub hp.asset hw
  rw [hr] at ho
  cases Result.ok.inj ho
  exact funext hm
#print axioms input

theorem nullifier (r : CopyRecords) (pub : R0P.Public K)
    (hw : WitnessOk (wordWitness r.w)) (hp : PubCorr (wordPublic r.p) pub)
    (d : Array U32 8#usize) (hd : CopyRecords.nullifier r = ok d) :
    digK d = R0P.nullifierHash (toModel (K := K) (wordWitness r.w)).sk
      (toModel (K := K) (wordWitness r.w)).salt := by
  unfold CopyRecords.nullifier at hd
  pv_peel hd with raw hr
  rw [PV_RunJoin_DigestIdentity30.digest] at hd
  cases Result.ok.inj hd
  rw [PV_Src_Forest_AuxContent.note_digest] at hr
  obtain ⟨out,ho,hm,_⟩ := PV_RunJoin_NullifierLift16.nullifier (wordWitness r.w) (wordPublic r.p) pub hp.asset hw
  simp only [UScalar.ofNatCore_val_eq] at hr
  rw [hr] at ho
  cases Result.ok.inj ho
  exact funext hm
#print axioms nullifier

theorem membership (r : CopyRecords) (pub : R0P.Public K)
    (hw : WitnessOk (wordWitness r.w)) (hp : PubCorr (wordPublic r.p) pub)
    (d : Array U32 8#usize) (hd : CopyRecords.path_digest r 24#usize = ok d) :
    digK d = R0P.merkleRoot
      (R0P.noteCommitment (R0P.ownerKey (toModel (K := K) (wordWitness r.w)).sk)
        ((toModel (K := K) (wordWitness r.w)).inputValue.val : K) pub.assetId
        (toModel (K := K) (wordWitness r.w)).salt)
      (toModel (K := K) (wordWitness r.w)).path := by
  unfold CopyRecords.path_digest at hd
  pv_peel hd with raw hr
  rw [PV_RunJoin_DigestIdentity30.digest] at hd
  cases Result.ok.inj hd
  rw [PV_Src_Forest_TreeArguments.tree _ _ _ (by decide)] at hr
  obtain ⟨out,ho,hm,_⟩ := PV_RunJoin_TreeLift16.tree (wordWitness r.w) (wordPublic r.p) pub hp.asset hw 24 (by omega)
  simp only [UScalar.ofNatCore_val_eq] at hr
  rw [hr] at ho
  cases Result.ok.inj ho
  have hmean := funext hm
  rw [BuilderSemanticBridge.treeCur_eq pub,BuilderSemanticBridge.inputLeaf_eq] at hmean
  exact hmean
#print axioms membership
end R1Z.PV_RunJoin_RecordInputLift31
