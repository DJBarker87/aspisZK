import R3SemanticEquationCore

/-! Exact remaining R3 joins: initial boundary sum, nine successive boundary
sums, and the terminal at the matching reader's Y. The ten degree obligations
are discharged symbolically by the literal coefficient parser. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
namespace AspisR1.R3SemanticRemainingJoins
open LiteralAcceptanceTerminal R0P.Mask R0C.SemStatement
open R3SemanticEquationCore
open R0P.SemSource
attribute [local irreducible] terminalZ maskClaimsR0 SpendDataMap.mapPublic

/-- This target is the existing masked terminal with precisely the HCHECKS
public, challenges, and four Y rows. It does not use a source-side surrogate. -/
def terminal (pub : R0P.Public SemanticPublicWire.M31)
    (view : LiteralOpeningView.View) (data : MatchingSupport.Data E) : E :=
  terminalZ (maskClaimsR0 ConcretePackBasis.basis)
    (SpendDataMap.mapPublic ExactBaseProjection.embed pub)
    ((view.semantic.map Prod.snd).getD 0 0)
    ((view.semantic.map Prod.snd).getD 1 0)
    ((view.semantic.map Prod.snd).getD 2 0)
    ((view.semantic.map Prod.snd).getD 13 0)
    ((view.semantic.map Prod.snd).getD 14 0)
    (preZc (fun j => (view.semantic.map Prod.snd).getD j.val 0))
    ConcretePackBasis.basis
    (fun j l => data.Y ⟨j.val, by omega⟩ l) (data.Y 3)
    (fun j => (view.semantic.map Prod.snd).getD (15 + j.val) 0)

/-- Remaining equation-only source joins. Successful parsing already proves
all ten degree guards, so no source degree-correctness join is required. -/
def EquationEndpoint (pub : R0P.Public SemanticPublicWire.M31)
    (rs : TranscriptRounds) (data : MatchingSupport.Data E) : Prop :=
  ∀ (view : LiteralOpeningView.View) (claim : E)
    (polynomials : Fin 10 → Polynomial E),
    LiteralOpeningView.read rs = some view →
    claimOf (SelectedSemanticPrefixFacts.lift view.semantic) = some claim →
    semPolysZ (SelectedSemanticPrefixFacts.lift view.semantic) = some polynomials →
    Equations claim (terminal pub view data)
      (fun j => (view.semantic.map Prod.snd).getD (15 + j.val) 0) polynomials

/-- The previous premise entails exactly the remaining arithmetic joins. -/
theorem equations_of_semantic (pub : R0P.Public SemanticPublicWire.M31)
    (rs : TranscriptRounds) (data : MatchingSupport.Data E)
    (h : HchecksReaderComposition.SemanticEndpoint pub rs data) :
    EquationEndpoint pub rs data := by
  intro view claim polys hopen hclaim hpolys
  exact (h view claim polys hopen hclaim hpolys).2

/-- Recover the original semantic endpoint without assuming any degree join. -/
theorem semantic_of_equations (pub : R0P.Public SemanticPublicWire.M31)
    (rs : TranscriptRounds) (data : MatchingSupport.Data E)
    (h : EquationEndpoint pub rs data) :
    HchecksReaderComposition.SemanticEndpoint pub rs data := by
  intro view claim polys hopen hclaim hpolys
  exact ⟨parsed_degrees rs view polys hopen hpolys,
    h view claim polys hopen hclaim hpolys⟩

#print axioms equations_of_semantic
#print axioms semantic_of_equations
end AspisR1.R3SemanticRemainingJoins
end
