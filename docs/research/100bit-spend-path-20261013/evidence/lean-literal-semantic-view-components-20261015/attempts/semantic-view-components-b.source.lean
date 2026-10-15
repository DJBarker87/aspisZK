import R1LiteralSemanticView

/-! Unfold the literal semantic view under its explicit successful readers.
This is a conditional representation identity for the semantic classifier;
it does not infer any reader success from acceptance or source execution. -/
set_option autoImplicit false
noncomputable section

namespace AspisR1.LiteralSemanticViewComponents

open R0P R0P.Mask R0P.SemSource
open AspisV8R15.ExactTowerBase
open AspisR1.LiteralTranscript
open AspisR1.TranscriptView
open AspisR1.LiteralSemanticView

theorem bad_iff_semanticBadZ
    (B : PackBasis LiteralSemanticView.F)
    (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message)
    (c : LiteralSemanticView.E)
    (hrow : P.round < 25)
    (pub : R0P.Public SemanticPublicWire.M31)
    (c1 : LiteralTranscript.C1Word)
    (rs : List (SemMsgZ LiteralSemanticView.E × LiteralSemanticView.E))
    (sm : SemMsgZ LiteralSemanticView.E)
    (hpub : SemanticPublicWire.parsePublic P.statement.pubBytes = some pub)
    (hc1 : LiteralTranscript.c1At
      (P.rounds ++ [(m, (TranscriptView.Value.ordinary 0, 0))]) = some c1)
    (hread : LiteralSemanticPrefix.read LiteralSemanticView.eK 0 P.rounds = some rs)
    (hmsg : LiteralSemanticPrefix.parseMessage LiteralSemanticView.eK
      ⟨P.round, hrow⟩ m = some sm) :
    LiteralSemanticView.bad B P m c ↔
      semanticBadZ (maskClaimsR0 B) B
        ⟨LiteralTypedContext.context ExactBaseProjection.embed LiteralSemanticView.eK
          (SpendDataMap.mapPublic ExactBaseProjection.embed pub)
          (PublicBaseMap.mapPublic_base ExactBaseProjection.embed pub) c1 (fun _ => 0),
          SelectedSemanticPrefixFacts.lift rs⟩ sm c := by
  have hview : LiteralSemanticView.read P m = some
      ⟨LiteralTypedContext.context ExactBaseProjection.embed LiteralSemanticView.eK
          (SpendDataMap.mapPublic ExactBaseProjection.embed pub)
          (PublicBaseMap.mapPublic_base ExactBaseProjection.embed pub) c1 (fun _ => 0),
        rs, LiteralSemanticPrefix.read_length LiteralSemanticView.eK 0 P.rounds rs hread,
        sm⟩ := by
    simp only [LiteralSemanticView.read, dif_pos hrow, hpub,
      Option.bind_eq_bind, Option.bind_some, hc1]
    split
    · rename_i hnone
      simp only [hread] at hnone
      cases hnone
    · rename_i rounds hparsed
      have heq : rounds = rs := Option.some.inj (hparsed.symm.trans hread)
      subst rounds
      simp only [hmsg, Option.bind_some]
  simp [LiteralSemanticView.bad, hview, LiteralSemanticView.View.prefix]

#print axioms bad_iff_semanticBadZ

end AspisR1.LiteralSemanticViewComponents
end
