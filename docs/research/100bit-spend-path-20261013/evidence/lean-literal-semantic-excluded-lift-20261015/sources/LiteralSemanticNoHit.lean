import R1LiteralSemanticViewComponents
import R1LiteralSemanticIndex
import R1LiteralSemanticTake
import R1LiteralC1Prefix
import R1LiteralClassifier
import R1GenericNoHitIndex
import R1LiteralIndexedPrefix

/-! Transport the literal classifier's no-hit condition to the parsed semantic
prefix, using the public statement and C1 actually read from that transcript.
Reader success remains explicit; no source acceptance or probability law is
asserted here. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralSemanticNoHit

open R0P R0P.Mask R0P.SemSource
open LiteralTranscript
abbrev E := LiteralSemanticView.E

attribute [local irreducible] LiteralClassifier.bad LiteralSemanticView.bad
  semanticBadZ

theorem parseMessage_valid
    (eK : AspisV8R15.ExactTowerBase.QM31Exact →+* E)
    (row : Fin 25) (m : Message) (sm : SemMsgZ E)
    (h : LiteralSemanticPrefix.parseMessage eK row m = some sm) :
    LiteralTranscript.valid row.val m := by
  by_contra hv
  simp only [LiteralSemanticPrefix.parseMessage, if_neg hv] at h
  cases h

/-- Every parsed semantic row excludes precisely the old masked semantic
bad event at its preceding parsed prefix and fixed literal context. -/
theorem parsed_events_excluded
    (pub : Public) (decoded : R0P.Public SemanticPublicWire.M31)
    (c1 : C1Word) (rs : List (Message × Challenge))
    (out : List (SemMsgZ E × E))
    (hpub : SemanticPublicWire.parsePublic pub.pubBytes = some decoded)
    (hc1 : LiteralTranscript.c1At rs = some c1)
    (hread : LiteralSemanticPrefix.read LiteralSemanticView.eK 0 rs = some out)
    (hno : ¬ GenericNoHit.hitFrom LiteralClassifier.bad pub [] rs) :
    ∀ i : Fin out.length,
      ¬ semanticBadZ (maskClaimsR0 ConcretePackBasis.basis) ConcretePackBasis.basis
        ⟨LiteralTypedContext.context ExactBaseProjection.embed LiteralSemanticView.eK
          (SpendDataMap.mapPublic ExactBaseProjection.embed decoded)
          (PublicBaseMap.mapPublic_base ExactBaseProjection.embed decoded) c1 (fun _ => 0),
          SelectedSemanticPrefixFacts.lift (out.take i.val)⟩
        (out[i.val]'i.isLt).1 (out[i.val]'i.isLt).2 := by
  intro i hbad
  have hlength := LiteralSemanticPrefix.read_length LiteralSemanticView.eK 0 rs out hread
  have hi : i.val < rs.length := by rw [← hlength]; exact i.isLt
  obtain ⟨hr, sm, c, hm, hv, ho⟩ :=
    LiteralSemanticIndex.read_index LiteralSemanticView.eK 0 rs out hread i.val hi
  let P : Prefix := ⟨pub, rs.take i.val⟩
  have hround : P.round = i.val := LiteralIndexedPrefix.take_prefix_round pub rs i.val hi
  have hr25 : P.round < 25 := by omega
  have hm' : LiteralSemanticPrefix.parseMessage LiteralSemanticView.eK
      ⟨P.round, hr25⟩ (rs[i.val].1) = some sm := by
    simpa only [hround, Nat.zero_add] using hm
  have hprefix : LiteralSemanticPrefix.read LiteralSemanticView.eK 0 P.rounds =
      some (out.take i.val) := LiteralSemanticTake.read_take _ _ _ _ hread i.val
  have hc1' : LiteralTranscript.c1At
      (P.rounds ++ [(rs[i.val].1, (TranscriptView.Value.ordinary 0, 0))]) = some c1 := by
    rw [LiteralC1Prefix.c1At_take_current rs i.val hi]
    exact hc1
  have hparsed : semanticBadZ (maskClaimsR0 ConcretePackBasis.basis) ConcretePackBasis.basis
      ⟨LiteralTypedContext.context ExactBaseProjection.embed LiteralSemanticView.eK
        (SpendDataMap.mapPublic ExactBaseProjection.embed decoded)
        (PublicBaseMap.mapPublic_base ExactBaseProjection.embed decoded) c1 (fun _ => 0),
        SelectedSemanticPrefixFacts.lift (out.take i.val)⟩ sm c := by
    simpa only [ho] using hbad
  have hview : LiteralSemanticView.bad ConcretePackBasis.basis P (rs[i.val].1) c :=
    (LiteralSemanticViewComponents.bad_iff_semanticBadZ ConcretePackBasis.basis P _ c
      hr25 decoded c1 (out.take i.val) sm hpub hc1' hprefix hm').mpr hparsed
  have hvalid := parseMessage_valid LiteralSemanticView.eK ⟨P.round, hr25⟩ _ sm hm'
  have hclass : LiteralClassifier.bad P (rs[i.val].1) (rs[i.val].2) := by
    simp only [LiteralClassifier.bad, if_pos hr25, LiteralSemanticDensity.event, hv]
    exact ⟨hvalid, hview⟩
  exact GenericNoHitIndex.not_bad_at_index LiteralClassifier.bad pub rs i.val hi hno hclass

#print axioms parseMessage_valid
#print axioms parsed_events_excluded

end AspisR1.LiteralSemanticNoHit
end
