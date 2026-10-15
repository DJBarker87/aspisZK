import R1SpendRelationMap
import R1ExactBaseProjection

/-! Explicit descent of an already valid wide-field witness whose coordinates
belong to the embedded base. The coordinate premise must be obtained from
candidate/trace typing; it is not inferred from spend validity alone. -/
set_option autoImplicit false
namespace AspisR1.SpendBaseDescent

open R0P SpendRelation AspisWideTower AspisV8R15.ExactTowerBase

abbrev E := WideExact
abbrev F := ExactBaseProjection.embed.fieldRange

structure BaseCoordinates (w : Witness E) : Prop where
  sk : ∀ i, w.sk i ∈ F
  salt : ∀ i, w.salt i ∈ F
  path : ∀ level i, (w.path level).2 i ∈ F
  first : ∀ i, w.pair.firstCommitment i ∈ F
  occupied : w.pair.secondOccupied ∈ F
  second : ∀ i, w.pair.secondCommitment i ∈ F
  inverse : w.pair.secondOccupancyInverse ∈ F
  recipientOwner : ∀ i, w.recipientOwner i ∈ F
  recipientSalt : ∀ i, w.recipientSalt i ∈ F
  changeOwner : ∀ i, w.changeOwner i ∈ F
  changeSalt : ∀ i, w.changeSalt i ∈ F

def projectWitness (w : Witness E) : Wspend :=
  SpendDataMap.witness ExactBaseProjection.project w

private theorem digest_recover (d : R0P.Digest E) (hd : ∀ i, d i ∈ F) :
    SpendDataMap.digest ExactBaseProjection.embed
      (SpendDataMap.digest ExactBaseProjection.project d) = d := by
  funext i
  exact ExactBaseProjection.embed_project_of_mem_fieldRange (hd i)

theorem witness_recover (w : Witness E) (h : BaseCoordinates w) :
    SpendDataMap.witness ExactBaseProjection.embed (projectWitness w) = w := by
  have hsk := digest_recover w.sk h.sk
  have hsalt := digest_recover w.salt h.salt
  have hro := digest_recover w.recipientOwner h.recipientOwner
  have hrs := digest_recover w.recipientSalt h.recipientSalt
  have hco := digest_recover w.changeOwner h.changeOwner
  have hcs := digest_recover w.changeSalt h.changeSalt
  have hpath : SpendDataMap.path ExactBaseProjection.embed
      (SpendDataMap.path ExactBaseProjection.project w.path) = w.path := by
    funext level
    apply Prod.ext
    · rfl
    · exact digest_recover (w.path level).2 (h.path level)
  have hpair : SpendDataMap.pair ExactBaseProjection.embed
      (SpendDataMap.pair ExactBaseProjection.project w.pair) = w.pair := by
    have hfirst := digest_recover w.pair.firstCommitment h.first
    have hsecond := digest_recover w.pair.secondCommitment h.second
    have hocc := ExactBaseProjection.embed_project_of_mem_fieldRange h.occupied
    have hinv := ExactBaseProjection.embed_project_of_mem_fieldRange h.inverse
    change { w.pair with
      firstCommitment := SpendDataMap.digest ExactBaseProjection.embed
        (SpendDataMap.digest ExactBaseProjection.project w.pair.firstCommitment)
      secondOccupied := ExactBaseProjection.embed (ExactBaseProjection.project w.pair.secondOccupied)
      secondCommitment := SpendDataMap.digest ExactBaseProjection.embed
        (SpendDataMap.digest ExactBaseProjection.project w.pair.secondCommitment)
      secondOccupancyInverse := ExactBaseProjection.embed
        (ExactBaseProjection.project w.pair.secondOccupancyInverse) } = w.pair
    rw [hfirst, hsecond, hocc, hinv]
  change { w with
    sk := SpendDataMap.digest ExactBaseProjection.embed
      (SpendDataMap.digest ExactBaseProjection.project w.sk)
    salt := SpendDataMap.digest ExactBaseProjection.embed
      (SpendDataMap.digest ExactBaseProjection.project w.salt)
    path := SpendDataMap.path ExactBaseProjection.embed
      (SpendDataMap.path ExactBaseProjection.project w.path)
    pair := SpendDataMap.pair ExactBaseProjection.embed
      (SpendDataMap.pair ExactBaseProjection.project w.pair)
    recipientOwner := SpendDataMap.digest ExactBaseProjection.embed
      (SpendDataMap.digest ExactBaseProjection.project w.recipientOwner)
    recipientSalt := SpendDataMap.digest ExactBaseProjection.embed
      (SpendDataMap.digest ExactBaseProjection.project w.recipientSalt)
    changeOwner := SpendDataMap.digest ExactBaseProjection.embed
      (SpendDataMap.digest ExactBaseProjection.project w.changeOwner)
    changeSalt := SpendDataMap.digest ExactBaseProjection.embed
      (SpendDataMap.digest ExactBaseProjection.project w.changeSalt) } = w
  rw [hsk, hsalt, hpath, hpair, hro, hrs, hco, hcs]

theorem rspend_project (pub : Public M31Exact) (w : Witness E)
    (hbase : BaseCoordinates w)
    (h : Rspend (SpendDataMap.mapPublic ExactBaseProjection.embed pub) w) :
    Rspend pub (projectWitness w) := by
  apply (SpendRelationMap.rspend_map_iff ExactBaseProjection.embed pub (projectWitness w)).mp
  rw [witness_recover w hbase]
  exact h

theorem check_project (pub : Public M31Exact) (w : Witness E)
    (hbase : BaseCoordinates w)
    (h : Rspend (SpendDataMap.mapPublic ExactBaseProjection.embed pub) w) :
    checkM31 pub (projectWitness w) = true :=
  (check_eq_true_iff pub (projectWitness w)).mpr (rspend_project pub w hbase h)

#print axioms witness_recover
#print axioms rspend_project
#print axioms check_project
end AspisR1.SpendBaseDescent
