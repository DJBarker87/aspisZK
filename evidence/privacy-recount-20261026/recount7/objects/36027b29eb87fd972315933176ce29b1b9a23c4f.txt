import R1Z.PV_RunJoin_RecordInputLift31
import R1Z.PV_RunJoin_CompilerReads31
import R1Z.PV_RunJoin_WitnessViews31
import R1Z.PV_RunJoin_CompilerReads30
import R1Z.PV_RunJoin_UniversalBuild22
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SemanticInput31
open Aeneas Aeneas.Std Result R0Z.WriterRefine R1J.SpendWitnessMap PV_Src_NativeInput
local instance : BuilderForestAdmissionPort.ExternalLinear := PV_RunJoin_ShippedExternal.E_shipped
local instance : BuilderForestAdmissionPort.Records := PV_RunJoin_UniversalRecords22.shipped
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

open PV_RunJoin_SemanticChange30

theorem nullifier (i : Input) (success : run i = ok (.Ok i.compiled))
    (checked : PV_Src_RecordReference.Checked i)
    (frontier : ∀ l : Fin 20, Canon8 i.snapshot.frontier.val[l.val]!) :
    (statement (K := K) i).nullifier = R0P.nullifierHash (witness (K := K) i).sk (witness (K := K) i).salt := by
  obtain ⟨r,hr,hread⟩ := PV_RunJoin_CompilerReads30.nullifier i.witness
    (outputValue i.request) (recipient i.request) i.change (forestPublic i.request)
    i.laneAnchor i.snapshot i.compiled success
  have hrecords : newRecords i = ok r := hr
  have hw := PV_RunJoin_UniversalRecords22.words i checked r hrecords
  have hp := PV_RunJoin_UniversalRecords22.publicCorr (K := K) i success frontier r hrecords
  have hpub : (statement (K := K) i).nullifier = digK (forestPublic i.request).nullifier := by
    cases hreq : i.request <;> funext j <;>
      simp only [statement,publicInput,forestPublic,hreq,PV_Src_Public.canonicalPublic,
        BuilderPublicProjection.transferPublic,BuilderPublicProjection.withdrawalPublic,
        mapPub,digK,liftU,map_natCast]
  rw [hpub]
  have hm := PV_RunJoin_RecordInputLift31.nullifier r (statement (K := K) i) hw hp _ hread
  rw [PV_RunJoin_UniversalRecords22.returned i r hrecords] at hm
  change _ = R0P.nullifierHash
    (BuilderSpendRelation.modelWitness (witness (K := K) i)).sk
    (BuilderSpendRelation.modelWitness (witness (K := K) i)).salt
  unfold witness
  rw [BuilderFieldNormalization.decoded_witness]
  exact hm
#print axioms nullifier

theorem membership (i : Input) (success : run i = ok (.Ok i.compiled))
    (checked : PV_Src_RecordReference.Checked i)
    (frontier : ∀ l : Fin 20, Canon8 i.snapshot.frontier.val[l.val]!) :
    (statement (K := K) i).anchor = R0P.merkleRoot (R0P.noteCommitment (R0P.ownerKey (witness (K := K) i).sk)
      ((witness (K := K) i).inputValue.val : K) (statement (K := K) i).assetId
      (witness (K := K) i).salt) (witness (K := K) i).path := by
  obtain ⟨r,hr,hread⟩ := PV_RunJoin_CompilerReads30.anchor i.witness
    (outputValue i.request) (recipient i.request) i.change (forestPublic i.request)
    i.laneAnchor i.snapshot i.compiled success
  have hrecords : newRecords i = ok r := hr
  have hw := PV_RunJoin_UniversalRecords22.words i checked r hrecords
  have hp := PV_RunJoin_UniversalRecords22.publicCorr (K := K) i success frontier r hrecords
  have hpub : (statement (K := K) i).anchor = digK (forestPublic i.request).anchor := by
    cases hreq : i.request <;> funext j <;>
      simp only [statement,publicInput,forestPublic,hreq,PV_Src_Public.canonicalPublic,
        BuilderPublicProjection.transferPublic,BuilderPublicProjection.withdrawalPublic,
        mapPub,digK,liftU,map_natCast]
  rw [hpub]
  have hm := PV_RunJoin_RecordInputLift31.membership r (statement (K := K) i) hw hp _ hread
  rw [PV_RunJoin_UniversalRecords22.returned i r hrecords] at hm
  change _ = R0P.merkleRoot (R0P.noteCommitment
    (R0P.ownerKey (BuilderSpendRelation.modelWitness (witness (K := K) i)).sk)
    ((BuilderSpendRelation.modelWitness (witness (K := K) i)).inputValue.val : K)
    (statement (K := K) i).assetId
    (BuilderSpendRelation.modelWitness (witness (K := K) i)).salt)
    (BuilderSpendRelation.modelWitness (witness (K := K) i)).path
  unfold witness
  rw [BuilderFieldNormalization.decoded_witness]
  exact hm
#print axioms membership

theorem sibling (i : Input) :
    ((witness (K := K) i).path 0).2 = if ((witness (K := K) i).path 0).1
      then (witness (K := K) i).pair.firstCommitment
      else (witness (K := K) i).pair.secondCommitment := by
  rw [PV_RunJoin_WitnessViews31.first_direction,
    PV_RunJoin_WitnessViews31.pair_first,PV_RunJoin_WitnessViews31.pair_second]
  exact PV_RunJoin_WitnessViews31.first_sibling i
#print axioms sibling

theorem commitment (i : Input) (success : run i = ok (.Ok i.compiled))
    (checked : PV_Src_RecordReference.Checked i)
    (frontier : ∀ l : Fin 20, Canon8 i.snapshot.frontier.val[l.val]!) :
    (witness (K := K) i).pair.selectedCommitment ((witness (K := K) i).path 0).1 =
      R0P.noteCommitment (R0P.ownerKey (witness (K := K) i).sk)
        ((witness (K := K) i).inputValue.val : K) (statement (K := K) i).assetId
        (witness (K := K) i).salt := by
  obtain ⟨r,d,hr,hd,hread⟩ := PV_RunJoin_CompilerReads31.input i.witness
    (outputValue i.request) (recipient i.request) i.change (forestPublic i.request)
    i.laneAnchor i.snapshot i.compiled success
  have hrecords : newRecords i = ok r := hr
  have hw := PV_RunJoin_UniversalRecords22.words i checked r hrecords
  have hp := PV_RunJoin_UniversalRecords22.publicCorr (K := K) i success frontier r hrecords
  have hm := PV_RunJoin_RecordInputLift31.input r (statement (K := K) i) hw hp d hread
  rw [PV_RunJoin_UniversalRecords22.returned i r hrecords] at hm
  have selected : (witness (K := K) i).pair.selectedCommitment ((witness (K := K) i).path 0).1 = digK d := by
    unfold AspisPool.V7PairLeafOccupancy.PairLeaf.selectedCommitment
    rw [PV_RunJoin_WitnessViews31.first_direction,
      PV_RunJoin_WitnessViews31.pair_first,PV_RunJoin_WitnessViews31.pair_second]
    unfold BuilderForestAdmissionPort.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1.selected_commitment at hd
    cases hbit : i.witness.pair.selected_second <;> simp only [hbit,Bool.false_eq_true,↓reduceIte] at hd ⊢
    all_goals cases Result.ok.inj hd; rfl
  rw [selected]
  change _ = R0P.noteCommitment
    (R0P.ownerKey (BuilderSpendRelation.modelWitness (witness (K := K) i)).sk)
    ((BuilderSpendRelation.modelWitness (witness (K := K) i)).inputValue.val : K)
    (statement (K := K) i).assetId
    (BuilderSpendRelation.modelWitness (witness (K := K) i)).salt
  unfold witness
  rw [BuilderFieldNormalization.decoded_witness]
  exact hm
#print axioms commitment
end R1Z.PV_RunJoin_SemanticInput31
