import OraclePortSemanticObservationsC6

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
namespace AspisR1.OraclePortSemanticProjectionC6
open LiteralAcceptanceTerminal R0P.Mask R0P.SemSource R0C.SemStatement
open OraclePortSemanticObservationsC6
attribute [local irreducible] R3SemanticRemainingJoins.terminal

/-- The semantic checker reads only these three projections. -/
structure Observation where
  challenges : List E
  claim : Option E
  polynomials : Option (Fin 10 → Polynomial E)

def observe (xs : List (SemMsgZ E × E)) : Observation :=
  ⟨xs.map Prod.snd,claimOf (SelectedSemanticPrefixFacts.lift xs),
    semPolysZ (SelectedSemanticPrefixFacts.lift xs)⟩

theorem scalar_challenges (xs : List (SemMsgZ E × E)) :
    (scalarPairs xs).map Prod.snd = xs.map Prod.snd := by
  simp only [scalarPairs,List.map_map,Function.comp_def]

theorem scalar_claim (xs : List (SemMsgZ E × E)) :
    claimOf (SelectedSemanticPrefixFacts.lift (scalarPairs xs)) =
      claimOf (SelectedSemanticPrefixFacts.lift xs) := by
  simp only [claimOf,SelectedSemanticPrefixFacts.lift,scalarPairs,List.getElem?_map]
  cases h : xs[14]? with
  | none => rfl
  | some mc =>
    rcases mc with ⟨m,c⟩
    cases m with
    | maskSum claim => rfl
    | base m => cases m <;> rfl

def poly : SemMsgZ E → Option (Polynomial E)
  | .base (.roundPoly p) => some p
  | _ => none

theorem scalar_poly (m : SemMsgZ E) : poly (scalarMessage m) = poly m := by
  cases m with
  | maskSum c => rfl
  | base m => cases m <;> rfl

theorem scalar_polynomials (xs : List (SemMsgZ E × E)) :
    semPolysZ (SelectedSemanticPrefixFacts.lift (scalarPairs xs)) =
      semPolysZ (SelectedSemanticPrefixFacts.lift xs) := by
  unfold SelectedSemanticPrefixFacts.lift scalarPairs
  unfold semPolysZ
  simp only [List.length_map,List.getElem_map]
  by_cases h : xs.length = 25
  · simp only [dif_pos h]
    have project (m : SemMsgZ E) :
        (match (Msg.semantic m : MsgZ E) with
          | .semantic (.base (.roundPoly p)) => some p
          | _ => none) = poly m := by
      cases m with
      | maskSum c => rfl
      | base m => cases m <;> rfl
    simp_rw [project,scalar_poly]

  · simp only [dif_neg h]

theorem observe_scalar (xs : List (SemMsgZ E × E)) : observe (scalarPairs xs) = observe xs := by
  unfold observe
  rw [scalar_challenges,scalar_claim,scalar_polynomials]

theorem observe_of_scalar_eq (xs ys : List (SemMsgZ E × E))
    (same : scalarPairs xs = scalarPairs ys) : observe xs = observe ys := by
  rw [← observe_scalar xs,← observe_scalar ys,same]

/-- Successful literal semantic readers can disagree on whole C2 words while
all equation-checker observations agree. -/
theorem read_observe (w : CanonicalCutEnrichedTranscript.Words) (offset : Nat)
    (rs : TranscriptRounds) (xs ys : List (SemMsgZ E × E))
    (left : LiteralSemanticPrefix.read LiteralOpeningView.eK offset rs = some xs)
    (right : LiteralSemanticPrefix.read LiteralOpeningView.eK offset
      (rs.map fun mc => (CanonicalCutEnrichedTranscript.enrichMessage w mc.1,mc.2)) = some ys) :
    observe ys = observe xs := by
  have same := read_scalar w offset rs
  rw [left,right] at same
  exact observe_of_scalar_eq ys xs (Option.some.inj same)

#print axioms scalar_challenges
#print axioms scalar_claim
#print axioms scalar_poly
#print axioms scalar_polynomials
#print axioms observe_scalar
#print axioms observe_of_scalar_eq
#print axioms read_observe
end AspisR1.OraclePortSemanticProjectionC6
end
