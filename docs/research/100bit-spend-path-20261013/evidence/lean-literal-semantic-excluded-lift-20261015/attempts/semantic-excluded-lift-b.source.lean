import R1LiteralSemanticNoHit

/-! Lift the exact parsed semantic-row exclusions to the literal semantic
transcript list. This is deterministic list/index plumbing only; no additional
semantic-hit equivalence or acceptance claim is made here. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralSemanticExcludedLift

open R0P R0P.Mask R0P.SemSource
open AspisR1.LiteralTranscript

abbrev E := LiteralSemanticNoHit.E

attribute [local irreducible] LiteralClassifier.bad semanticBadZ

theorem excluded_lift
    (pub : Public) (decoded : R0P.Public SemanticPublicWire.M31)
    (c1 : C1Word) (rs : List (Message × Challenge))
    (out : List (SemMsgZ E × E))
    (hpub : SemanticPublicWire.parsePublic pub.pubBytes = some decoded)
    (hc1 : LiteralTranscript.c1At rs = some c1)
    (hread : LiteralSemanticPrefix.read LiteralSemanticView.eK 0 rs = some out)
    (hno : ¬ GenericNoHit.hitFrom LiteralClassifier.bad pub [] rs) :
    ∀ i : Fin (SelectedSemanticPrefixFacts.lift out).length,
      ∀ sm,
        ((SelectedSemanticPrefixFacts.lift out)[i.val]'i.isLt).1 =
          R0C.SemStatement.Msg.semantic sm →
        ¬ semanticBadZ (maskClaimsR0 ConcretePackBasis.basis) ConcretePackBasis.basis
          ⟨LiteralTypedContext.context ExactBaseProjection.embed LiteralSemanticView.eK
            (SpendDataMap.mapPublic ExactBaseProjection.embed decoded)
            (PublicBaseMap.mapPublic_base ExactBaseProjection.embed decoded) c1 (fun _ => 0),
            (SelectedSemanticPrefixFacts.lift out).take i.val⟩
          sm ((out.map Prod.snd).getD i.val 0) := by
  intro i sm hmessage
  have hiout : i.val < out.length := by
    simpa [SelectedSemanticPrefixFacts.lift] using i.isLt
  let iout : Fin out.length := ⟨i.val, hiout⟩
  have hnot := LiteralSemanticNoHit.parsed_events_excluded
    pub decoded c1 rs out hpub hc1 hread hno iout
  have hmessage' :
      (R0C.SemStatement.Msg.semantic (out[i.val]'iout.isLt).1 : MsgZ E) =
        R0C.SemStatement.Msg.semantic sm := by
    simpa [SelectedSemanticPrefixFacts.lift, iout] using hmessage
  have hsm : (out[i.val]'iout.isLt).1 = sm :=
    R0C.SemStatement.Msg.semantic.inj hmessage'
  subst sm
  have hchal : (out.map Prod.snd).getD i.val 0 = (out[i.val]'iout.isLt).2 := by
    rw [List.getD_eq_getElem (by simpa only [List.length_map] using hiout)]
    simp only [List.getElem_map]
  have htake :
      (SelectedSemanticPrefixFacts.lift out).take i.val =
        SelectedSemanticPrefixFacts.lift (out.take i.val) := by
    simp [SelectedSemanticPrefixFacts.lift]
  simpa only [htake, hchal] using hnot

#print axioms excluded_lift

end AspisR1.LiteralSemanticExcludedLift
end
