import HchecksReaderComposition

/-! R3's field equations, separated from the ten degree guards. The literal
coefficient parser supplies the guards; acceptance of a free byte decision
supplies no field equation. No source or extracted module is changed. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.R3SemanticEquationCore
open LiteralAcceptanceTerminal R0P.Mask

/-- Arithmetic joins left after coefficient shape has supplied degree bounds. -/
def Equations {K : Type} [CommSemiring K] (claim terminal : K)
    (alpha : Fin 10 → K) (polys : Fin 10 → Polynomial K) : Prop :=
  (polys 0).eval 0 + (polys 0).eval 1 = claim ∧
  (∀ j : Fin 9, (polys j.succ).eval 0 + (polys j.succ).eval 1 =
    (polys j.castSucc).eval (alpha j.castSucc)) ∧
  (polys 9).eval (alpha 9) = terminal

/-- Degree follows from successful opening and polynomial readers, even on a
rejected transcript. No semantic acceptance or Rust arithmetic is assumed. -/
theorem parsed_degrees (rs : TranscriptRounds) (view : LiteralOpeningView.View)
    (polynomials : Fin 10 → Polynomial E)
    (hopen : LiteralOpeningView.read rs = some view)
    (hpolys : semPolysZ (SelectedSemanticPrefixFacts.lift view.semantic) =
      some polynomials) :
    ∀ j : Fin 10, (polynomials j).natDegree ≤ 27 := by
  obtain ⟨hlen, _, hc2, hsem, _⟩ :=
    LiteralOpeningPrefixFacts.read_prefix_components rs view hopen
  obtain ⟨payloads, challenges, _, _, _, _, hp, hd⟩ :=
    LiteralSemanticParserFacts.read_projection_facts
      LiteralOpeningView.eK (rs.take 25) view.semantic view.c2 hsem hlen hc2
  have heq := Option.some.inj (hpolys.symm.trans hp)
  rw [heq]
  exact hd

#print axioms parsed_degrees
end AspisR1.R3SemanticEquationCore
end
