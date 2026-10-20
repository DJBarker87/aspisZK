import R3SemanticRemainingJoins
import R3SemanticChainProjection

/-! Consumer of an R2 chain after identification with the compiled reader.
The arithmetic certificate is not assumed to identify its source endpoints or
ordered challenges by name alone. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.R3SemanticChainEndpoint
open LiteralAcceptanceTerminal R0P.Mask
open AspisR1PublicPreparation.RawGenericPolynomialSumcheckChain

/-- Once the source R2 chain has this exact start, terminal and ordered list,
no additional sumcheck equation or degree hypothesis is necessary. -/
theorem endpoint_of_identified_chains
    (pub : R0P.Public SemanticPublicWire.M31) (rs : TranscriptRounds)
    (data : MatchingSupport.Data E)
    (hchain : ∀ (view : LiteralOpeningView.View) (claim : E)
      (polynomials : Fin 10 → Polynomial E),
      LiteralOpeningView.read rs = some view →
      claimOf (SelectedSemanticPrefixFacts.lift view.semantic) = some claim →
      semPolysZ (SelectedSemanticPrefixFacts.lift view.semantic) = some polynomials →
      Chain claim (R3SemanticRemainingJoins.terminal pub view data)
        (List.ofFn fun j : Fin 10 =>
          (polynomials j, (view.semantic.map Prod.snd).getD (15 + j.val) 0))) :
    HchecksReaderComposition.SemanticEndpoint pub rs data := by
  apply R3SemanticRemainingJoins.semantic_of_equations
  intro view claim polys hopen hclaim hpolys
  exact R3SemanticChainProjection.equations_of_chain _ _ _ _
    (hchain view claim polys hopen hclaim hpolys)

#print axioms endpoint_of_identified_chains
end AspisR1.R3SemanticChainEndpoint
end
