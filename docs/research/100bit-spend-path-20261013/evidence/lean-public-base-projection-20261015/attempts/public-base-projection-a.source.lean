import R1SpendRelationMap
import R1ExactBaseProjection
import R1SpendBaseDescent
import R0P.CoreExt

set_option autoImplicit false
namespace AspisR1.PublicBaseProjection

open R0P AspisWideTower AspisV8R15.ExactTowerBase

abbrev E := WideExact
abbrev F := ExactBaseProjection.embed.fieldRange

def projectPublic (pub : Public E) : Public M31Exact :=
  SpendDataMap.mapPublic ExactBaseProjection.project pub

private theorem digest_recover (d : Digest E) (hd : ∀ i, d i ∈ F) :
    SpendDataMap.digest ExactBaseProjection.embed
      (SpendDataMap.digest ExactBaseProjection.project d) = d := by
  funext i
  exact ExactBaseProjection.embed_project_of_mem_fieldRange (hd i)

theorem publicBase_map (pub : Public M31Exact) :
    PublicBase F (SpendDataMap.mapPublic ExactBaseProjection.embed pub) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ExactBaseProjection.embed.mem_fieldRange_self _
  · intro i
    exact ExactBaseProjection.embed.mem_fieldRange_self _
  · exact ExactBaseProjection.embed.mem_fieldRange_self _
  · intro r hr i
    change pub.recipient.map (SpendDataMap.digest ExactBaseProjection.embed) = some r at hr
    cases hv : pub.recipient with
    | none => simp only [hv, Option.map_none] at hr; cases hr
    | some d =>
        have heq : SpendDataMap.digest ExactBaseProjection.embed d = r := by
          simpa only [hv, Option.map_some, Option.some.injEq] using hr
        rw [← heq]
        exact ExactBaseProjection.embed.mem_fieldRange_self _
  · intro i
    exact ExactBaseProjection.embed.mem_fieldRange_self _
  · intro a ha
    change pub.withdrawalAmount.map ExactBaseProjection.embed = some a at ha
    cases hv : pub.withdrawalAmount with
    | none => simp only [hv, Option.map_none] at ha; cases ha
    | some x =>
        have heq : ExactBaseProjection.embed x = a := by
          simpa only [hv, Option.map_some, Option.some.injEq] using ha
        rw [← heq]
        exact ExactBaseProjection.embed.mem_fieldRange_self _
  · intro l i
    exact ExactBaseProjection.embed.mem_fieldRange_self _
  · intro i
    exact ExactBaseProjection.embed.mem_fieldRange_self _
  · intro l i
    exact ExactBaseProjection.embed.mem_fieldRange_self _

theorem project_map (pub : Public M31Exact) :
    projectPublic (SpendDataMap.mapPublic ExactBaseProjection.embed pub) = pub := by
  unfold projectPublic
  rw [SpendDataMap.mapPublic_comp]
  have hfun : ExactBaseProjection.project ∘
      (ExactBaseProjection.embed : M31Exact → E) = id := by
    funext x
    exact ExactBaseProjection.project_embed x
  rw [hfun, SpendDataMap.mapPublic_id]

theorem embed_project (pub : Public E) (hbase : PublicBase F pub) :
    SpendDataMap.mapPublic ExactBaseProjection.embed (projectPublic pub) = pub := by
  rcases hbase with ⟨ha, hn, has, hr, hc, hw, hf, hroot, hnext⟩
  have ha' := digest_recover pub.anchor ha
  have hn' := digest_recover pub.nullifier hn
  have has' := ExactBaseProjection.embed_project_of_mem_fieldRange has
  have hc' := digest_recover pub.change hc
  have hroot' := digest_recover pub.nextRoot hroot
  have hr' : (pub.recipient.map (SpendDataMap.digest ExactBaseProjection.project)).map
      (SpendDataMap.digest ExactBaseProjection.embed) = pub.recipient := by
    cases hv : pub.recipient with
    | none => simp only [hv, Option.map_none]
    | some d =>
        simp only [hv, Option.map_some]
        exact congrArg some (digest_recover d (hr d hv))
  have hw' : (pub.withdrawalAmount.map ExactBaseProjection.project).map
      ExactBaseProjection.embed = pub.withdrawalAmount := by
    cases hv : pub.withdrawalAmount with
    | none => simp only [hv, Option.map_none]
    | some x =>
        simp only [hv, Option.map_some]
        exact congrArg some (ExactBaseProjection.embed_project_of_mem_fieldRange (hw x hv))
  have hf' : (fun l => SpendDataMap.digest ExactBaseProjection.embed
      (SpendDataMap.digest ExactBaseProjection.project (pub.snapshotFrontier l))) =
      pub.snapshotFrontier := by
    funext l
    exact digest_recover (pub.snapshotFrontier l) (hf l)
  have hnext' : (fun l => SpendDataMap.digest ExactBaseProjection.embed
      (SpendDataMap.digest ExactBaseProjection.project (pub.nextFrontier l))) =
      pub.nextFrontier := by
    funext l
    exact digest_recover (pub.nextFrontier l) (hnext l)
  change { pub with
    anchor := SpendDataMap.digest ExactBaseProjection.embed
      (SpendDataMap.digest ExactBaseProjection.project pub.anchor)
    nullifier := SpendDataMap.digest ExactBaseProjection.embed
      (SpendDataMap.digest ExactBaseProjection.project pub.nullifier)
    assetId := ExactBaseProjection.embed (ExactBaseProjection.project pub.assetId)
    recipient := (pub.recipient.map (SpendDataMap.digest ExactBaseProjection.project)).map
      (SpendDataMap.digest ExactBaseProjection.embed)
    change := SpendDataMap.digest ExactBaseProjection.embed
      (SpendDataMap.digest ExactBaseProjection.project pub.change)
    withdrawalAmount := (pub.withdrawalAmount.map ExactBaseProjection.project).map
      ExactBaseProjection.embed
    snapshotFrontier := fun l => SpendDataMap.digest ExactBaseProjection.embed
      (SpendDataMap.digest ExactBaseProjection.project (pub.snapshotFrontier l))
    nextRoot := SpendDataMap.digest ExactBaseProjection.embed
      (SpendDataMap.digest ExactBaseProjection.project pub.nextRoot)
    nextFrontier := fun l => SpendDataMap.digest ExactBaseProjection.embed
      (SpendDataMap.digest ExactBaseProjection.project (pub.nextFrontier l)) } = pub
  rw [ha', hn', has', hr', hc', hw', hf', hroot', hnext']

theorem publicBase_iff_embed_project (pub : Public E) :
    PublicBase F pub ↔
      SpendDataMap.mapPublic ExactBaseProjection.embed (projectPublic pub) = pub := by
  constructor
  · exact embed_project pub
  · intro h
    rw [← h]
    exact publicBase_map (projectPublic pub)

theorem canonical_project_iff (pub : Public E) (hbase : PublicBase F pub) :
    PublicOptionShape.canonical (projectPublic pub) ↔
      PublicOptionShape.canonical pub := by
  have h := SpendRelationMap.canonical_map_iff ExactBaseProjection.embed
    ExactBaseProjection.embed.injective (projectPublic pub)
  rw [embed_project pub hbase] at h
  exact h.symm

theorem optionCheck_project_iff (pub : Public E) (hbase : PublicBase F pub) :
    PublicOptionShape.check (projectPublic pub) = true ↔
      PublicOptionShape.check pub = true := by
  rw [PublicOptionShape.check_eq_true_iff, PublicOptionShape.check_eq_true_iff]
  exact canonical_project_iff pub hbase

theorem rspend_mapped_witness_iff (pub : Public E) (hbase : PublicBase F pub)
    (w : SpendRelation.Wspend) :
    SpendRelation.Rspend pub (SpendDataMap.witness ExactBaseProjection.embed w) ↔
      SpendRelation.Rspend (projectPublic pub) w := by
  have h := SpendRelationMap.rspend_map_iff ExactBaseProjection.embed
    (projectPublic pub) w
  rw [embed_project pub hbase] at h
  exact h

theorem rspend_project (pub : Public E) (w : SpendRelation.Witness E)
    (hpub : PublicBase F pub) (hw : SpendBaseDescent.BaseCoordinates w)
    (h : SpendRelation.Rspend pub w) :
    SpendRelation.Rspend (projectPublic pub) (SpendBaseDescent.projectWitness w) := by
  apply SpendBaseDescent.rspend_project (projectPublic pub) w hw
  rw [embed_project pub hpub]
  exact h

theorem spendCheck_project (pub : Public E) (w : SpendRelation.Witness E)
    (hpub : PublicBase F pub) (hw : SpendBaseDescent.BaseCoordinates w)
    (h : SpendRelation.Rspend pub w) :
    SpendRelation.checkM31 (projectPublic pub) (SpendBaseDescent.projectWitness w) = true :=
  (SpendRelation.check_eq_true_iff (projectPublic pub)
    (SpendBaseDescent.projectWitness w)).mpr (rspend_project pub w hpub hw h)

#print axioms publicBase_map
#print axioms project_map
#print axioms embed_project
#print axioms publicBase_iff_embed_project
#print axioms canonical_project_iff
#print axioms optionCheck_project_iff
#print axioms rspend_mapped_witness_iff
#print axioms rspend_project
#print axioms spendCheck_project
end AspisR1.PublicBaseProjection
