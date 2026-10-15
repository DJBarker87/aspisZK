import R1SemanticPrefix
import R1LiteralOpeningDataRows
import R1SelectedOpeningFunctionals

/-! Generic fallback for the literal opening-row bridge. This transports
matching-data predicates through the already checked generic `withRows`
identity before applying the existing semantic-prefix theorem. It adds no
source-refinement or acceptance claim. -/
set_option autoImplicit false
noncomputable section

namespace AspisR1.LiteralSemanticTerminalBridge

open R0P R0P.SemSource R0P.Mask R0P.SemRounds R0C.SemStatement Polynomial
open AspisCircleGroupOrder
open AspisR1.MatchingSupport

attribute [local irreducible] ConcreteBinding.candidates MatchingSupport.Good
  MatchingSupport.AcceptedPairing MatchingSupport.matchingSet sumcheckChecksZ
  SelectedOpeningFunctionals.functionals SelectedOpeningFunctionals.rawBase
  SelectedOpeningFunctionals.rows RawOpening.withRows

variable {E : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod P) E]

theorem large_matching_extracts_of_literal_prefix
    (prime : Nat) [CharP E prime] (hprime : prime = 2^31-1)
    (S : Fin 29 → Subfield E) (F : Subfield E)
    (lanesF : ∀ l : Fin 29, l.val < 26 → S l = F) (B : PackBasis F)
    (x : TypedContext E S) (htransport : x.transport = AspisR1.rowEquiv)
    (pubTyped : PublicBase F x.pub)
    (d : MatchingSupport.Data E) (typed : CandidateDescent.WordTyped S d.W)
    (fallback : AspisR0.ChordGeometry.Point E)
    (rs : List (MsgZ E × ChalZ E)) (hlen : rs.length = 25)
    (cs : List E) (hparse : semChalsZ rs = some cs)
    (claim : E) (hclaim : claimOf rs = some claim)
    (polys : Fin 10 → E[X]) (hpolys : semPolysZ rs = some polys)
    (hw gw : InitialWord E) (hc2 : c2OfZ rs = some (hw, gw))
    (hwords : d.W = c2Words x hw gw)
    (hexcluded : ∀ i : Fin rs.length, ∀ sm,
      (rs[i.val]'i.isLt).1 = .semantic sm →
        ¬ semanticBadZ (maskClaimsR0 B) B ⟨x, rs.take i.val⟩ sm (cs.getD i.val 0))
    (z : Fin 2 → AspisR0.ChordGeometry.Point E)
    (hF : d.F = SelectedOpeningFunctionals.functionals cs z)
    (hF0 : d.F0 = SelectedOpeningFunctionals.rawBase cs z)
    (hgood : MatchingSupport.Good d)
    (haccepted : MatchingSupport.AcceptedPairing d)
    (hcard : 9558 ≤ (MatchingSupport.matchingSet d).card)
    (checks : sumcheckChecksZ (maskClaimsR0 B) x.pub B
      (fun j => cs.getD j.val 0) (cs.getD 14 0) claim
      (fun j => cs.getD (15 + j.val) 0) polys
      (fun j l => d.Y ⟨j.val, by omega⟩ l) (d.Y 3)) :
    ∃ m ∈ ConcreteBinding.candidates d.W,
      (ProductionHolds x.pub (cs.getD 0 0) (cs.getD 1 0) (rowsOf AspisR1.rowEquiv m) ∧
        CopyLinkBalance x.pub (rowsOf AspisR1.rowEquiv m)) ∧
      InputNoteExtracted x.pub (rowsOf AspisR1.rowEquiv m) := by
  have hdata := LiteralOpeningDataRows.withRows_eq_self d cs z hF hF0
  have hgood' := hgood
  have haccepted' := haccepted
  have hcard' := hcard
  rw [← hdata] at hgood' haccepted' hcard'
  have hraw : SelectedOpeningFunctionals.rows cs z =
      SemanticOpening.rows R0P.copyInactiveRows
        (SemanticTransport.points (fun j : Fin 10 => cs.getD (15 + j.val) 0))
        (SemSource.libraWeight (fun j : Fin 10 => cs.getD (15 + j.val) 0))
        (SelectedOpeningFunctionals.circle z) := by
    unfold SelectedOpeningFunctionals.rows SelectedOpeningFunctionals.alpha
    rfl
  rw [hraw] at hgood' haccepted' hcard'
  exact SemanticPrefix.large_matching_extracts_of_prefix
    prime hprime S F lanesF B x htransport pubTyped d typed fallback rs hlen cs hparse
    claim hclaim polys hpolys hw gw hc2 hwords hexcluded
    R0P.copyInactiveRows (SelectedOpeningFunctionals.circle z)
    hgood' haccepted' hcard'
    checks

#print axioms large_matching_extracts_of_literal_prefix

end AspisR1.LiteralSemanticTerminalBridge
end
