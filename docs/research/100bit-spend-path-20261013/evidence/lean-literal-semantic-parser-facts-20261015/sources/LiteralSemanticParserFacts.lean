import R1LiteralSemanticPairs
import R1SelectedSemanticPrefixFacts

/-! Projection facts from a successful literal semantic parse to its
canonical typed-payload rounds. These are model equalities only; they do not
assert acceptance, source correspondence, or probability bounds. -/
set_option autoImplicit false
noncomputable section

namespace AspisR1.LiteralSemanticParserFacts

open AspisR1.LiteralSemanticPairs
open AspisR1.SemanticPayloadView
open AspisR1.SelectedSemanticPrefixFacts
open R0P.Mask

abbrev E := AspisR1.LiteralSemanticPrefix.E

theorem read_lift_eq_rounds
    (eK : AspisV8R15.ExactTowerBase.QM31Exact →+* E)
    (rs : List (AspisR1.LiteralTranscript.Message × AspisR1.LiteralTranscript.Challenge))
    (out : List (SemMsgZ E × E))
    (word : AspisR1.LiteralTranscript.C2Word)
    (hread : AspisR1.LiteralSemanticPrefix.read eK 0 rs = some out)
    (hlen : rs.length = 25)
    (hc2 : AspisR1.LiteralTranscript.c2At rs = some word) :
    ∃ payloads : (i : Fin 25) → AspisR1.SemanticRecordCodec.RowPayload i,
    ∃ challenges : Fin 25 → E,
      lift out = rounds (fun _ => AspisR1.LiteralSemanticPrefix.c2Pair eK word)
        payloads challenges := by
  obtain ⟨payloads, challenges, hout⟩ :=
    LiteralSemanticPairs.read_eq_pairs eK rs out word hread hlen hc2
  refine ⟨payloads, challenges, ?_⟩
  rw [hout]
  rfl

theorem read_projection_facts
    (eK : AspisV8R15.ExactTowerBase.QM31Exact →+* E)
    (rs : List (AspisR1.LiteralTranscript.Message × AspisR1.LiteralTranscript.Challenge))
    (out : List (SemMsgZ E × E))
    (word : AspisR1.LiteralTranscript.C2Word)
    (hread : AspisR1.LiteralSemanticPrefix.read eK 0 rs = some out)
    (hlen : rs.length = 25)
    (hc2 : AspisR1.LiteralTranscript.c2At rs = some word) :
    ∃ payloads : (i : Fin 25) → AspisR1.SemanticRecordCodec.RowPayload i,
    ∃ challenges : Fin 25 → E,
      lift out = rounds (fun _ => AspisR1.LiteralSemanticPrefix.c2Pair eK word)
        payloads challenges ∧
      semChalsZ (lift out) = some (List.ofFn challenges) ∧
      c2OfZ (lift out) = some
        (AspisR1.LiteralSemanticPrefix.c2Pair eK word) ∧
      claimOf (lift out) = some (claimAt14 payloads) ∧
      semPolysZ (lift out) = some
        (fun j => SemanticCoefficientCodec.polynomial (coeffAt payloads j)) ∧
      ∀ j, ((SemanticCoefficientCodec.polynomial (coeffAt payloads j) : Polynomial E).natDegree ≤ 27) := by
  obtain ⟨payloads, challenges, hout⟩ :=
    read_lift_eq_rounds eK rs out word hread hlen hc2
  refine ⟨payloads, challenges, hout, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hout] using
      (SemanticPayloadView.semChalsZ_rounds
        (fun _ => AspisR1.LiteralSemanticPrefix.c2Pair eK word)
        payloads challenges)
  · simpa [hout] using
      (SemanticPayloadView.c2OfZ_rounds
        (fun _ => AspisR1.LiteralSemanticPrefix.c2Pair eK word)
        payloads challenges)
  · simpa [hout] using
      (SemanticPayloadView.claimOf_rounds
        (fun _ => AspisR1.LiteralSemanticPrefix.c2Pair eK word)
        payloads challenges)
  · simpa [hout] using
      (SemanticPayloadView.semPolysZ_rounds
        (fun _ => AspisR1.LiteralSemanticPrefix.c2Pair eK word)
        payloads challenges)
  · intro j
    exact SemanticPayloadView.polynomial_degree payloads j

#print axioms read_lift_eq_rounds
#print axioms read_projection_facts

end AspisR1.LiteralSemanticParserFacts
end
