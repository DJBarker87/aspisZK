import R1PublicBaseProjection
import R1TraceWitnessExtract

set_option autoImplicit false
namespace AspisR1.PublicBaseProjection
open R0P AspisWideTower AspisV8R15.ExactTowerBase

theorem extract_complete_of_typed_public
    (pub : Public E) (A : Trace E) (lam chi : E)
    (hpub : PublicBase F pub) (hshape : PublicOptionShape.canonical pub)
    (hbase : BaseTyped F A)
    (h : ProductionHolds pub lam chi A ∧ CopyLinkBalance pub A) :
    ∃ w : SpendRelation.Wspend,
      TraceWitnessExtract.extract (projectPublic pub) A = some w ∧
      SpendRelation.Rspend (projectPublic pub) w := by
  have hshape' := (canonical_project_iff pub hpub).mpr hshape
  have h' : ProductionHolds
      (SpendDataMap.mapPublic ExactBaseProjection.embed (projectPublic pub)) lam chi A ∧
      CopyLinkBalance
        (SpendDataMap.mapPublic ExactBaseProjection.embed (projectPublic pub)) A := by
    simpa only [embed_project pub hpub] using h
  exact TraceWitnessExtract.complete_of_production
    (projectPublic pub) A lam chi hshape' hbase h'

#print axioms extract_complete_of_typed_public
end AspisR1.PublicBaseProjection
