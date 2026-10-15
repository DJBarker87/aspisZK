import R1LiteralSemanticNoHit
import R1SemanticHit

/-! Lift the parsed semantic-row exclusion to the exact literal semantic
transcript list. Reader success and the no-hit premise remain explicit; this
is not an accepted-execution or terminal D3 theorem. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralSemanticLiftNoHit

open R0P R0P.Mask R0P.SemSource
open AspisR1.LiteralTranscript

abbrev E := LiteralSemanticNoHit.E

attribute [local irreducible] LiteralClassifier.bad semanticBadZ

theorem no_hit_lift
    (pub : Public) (decoded : R0P.Public SemanticPublicWire.M31)
    (c1 : C1Word) (rs : List (Message × Challenge))
    (out : List (SemMsgZ E × E))
    (fallback : AspisR0.ChordGeometry.Point E)
    (hpub : SemanticPublicWire.parsePublic pub.pubBytes = some decoded)
    (hc1 : LiteralTranscript.c1At rs = some c1)
    (hread : LiteralSemanticPrefix.read LiteralSemanticView.eK 0 rs = some out)
    (hno : ¬ GenericNoHit.hitFrom LiteralClassifier.bad pub [] rs) :
    ¬ R0P.Mask.hitFrom
      (sourceDataWithFallbackZ fallback (maskClaimsR0 ConcretePackBasis.basis)
        ConcretePackBasis.basis)
      (LiteralTypedContext.context ExactBaseProjection.embed LiteralSemanticView.eK
        (SpendDataMap.mapPublic ExactBaseProjection.embed decoded)
        (PublicBaseMap.mapPublic_base ExactBaseProjection.embed decoded) c1 (fun _ => 0))
      [] (SelectedSemanticPrefixFacts.lift out) := by
  have hlen : out.length ≤ 25 := by
    by_contra hgt
    have hreadlen := LiteralSemanticPrefix.read_length LiteralSemanticView.eK 0 rs out hread
    have hrs : 25 < rs.length := by omega
    obtain ⟨hrow, _, _, _, _, _⟩ :=
      LiteralSemanticIndex.read_index LiteralSemanticView.eK 0 rs out hread 25 hrs
    omega
  have hparse := SelectedSemanticPrefixFacts.semChalsZ_lift out
  apply (SemanticHit.no_hitFrom_iff_all_semanticBadZ_excluded
    (LiteralTypedContext.context ExactBaseProjection.embed LiteralSemanticView.eK
      (SpendDataMap.mapPublic ExactBaseProjection.embed decoded)
      (PublicBaseMap.mapPublic_base ExactBaseProjection.embed decoded) c1 (fun _ => 0))
    fallback (maskClaimsR0 ConcretePackBasis.basis) ConcretePackBasis.basis
    (SelectedSemanticPrefixFacts.lift out) (out.map Prod.snd) hparse (by
      simpa [SelectedSemanticPrefixFacts.lift] using hlen)).2
  intro i sm hmessage
  have hiout : i.val < out.length := by
    simpa [SelectedSemanticPrefixFacts.lift] using i.isLt
  let iout : Fin out.length := ⟨i.val, hiout⟩
  have hnot := LiteralSemanticNoHit.parsed_events_excluded
    pub decoded c1 rs out hpub hc1 hread hno iout
  have hmessage' :
      R0C.SemStatement.Msg.semantic (out[i.val]'iout.isLt).1 =
        R0C.SemStatement.Msg.semantic sm := by
    simpa [SelectedSemanticPrefixFacts.lift, iout] using hmessage
  have hsm : (out[i.val]'iout.isLt).1 = sm :=
    R0C.SemStatement.Msg.semantic.inj hmessage'
  subst sm
  have hchal : (out.map Prod.snd).getD i.val 0 = (out[i.val]'iout.isLt).2 := by
    simp [iout]
  have htake :
      (SelectedSemanticPrefixFacts.lift out).take i.val =
        SelectedSemanticPrefixFacts.lift (out.take i.val) := by
    simp [SelectedSemanticPrefixFacts.lift]
  simpa only [htake, hchal] using hnot

#print axioms no_hit_lift

end AspisR1.LiteralSemanticLiftNoHit
end
