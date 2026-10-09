import SourcePolynomialEndpointObstruction

/-! A correct generic endpoint for the selected semantic source polynomial.

The source object is represented by its causal univariate restrictions.  A
round-`r` message receives exactly the `r` preceding challenges.  Its laws are
the ordinary Boolean partial-sum boundary and an individual degree bound.
The final source evaluation is *defined by the same last restriction*, so the
endpoint theorem below is derived, not stored in a structure field.

Instantiating this interface with the literal pair-forest `payment_terminal`
and proving its restriction/boundary laws remains a separate source theorem.
-/
set_option autoImplicit false
set_option Elab.async false
namespace AspisV8Completion.CausalSourcePolynomialTrace
open scoped BigOperators
open Polynomial
open AspisV6TranscriptRelationGrammar
open AspisV8.SelectedCompactSemanticRepair

variable {K : Type*} [Field K] [DecidableEq K]

/-- The challenges visible before source round `round`. -/
def sourceHistory (point : Fin 10 → K) (round : Fin 10) : List K :=
  List.ofFn fun earlier : Fin round.val =>
    point ⟨earlier.val, lt_trans earlier.isLt round.isLt⟩

@[simp] theorem sourceHistory_length (point : Fin 10 → K) (round : Fin 10) :
    (sourceHistory point round).length = round.val := by
  simp [sourceHistory]

/-- Adding the next challenge extends, rather than retrospectively changes,
the previously visible history. -/
theorem sourceHistory_succ (point : Fin 10 → K) (previous : Fin 9) :
    sourceHistory point previous.succ =
      (sourceHistory point previous.castSucc).concat (point previous.castSucc) := by
  unfold sourceHistory
  change
    List.ofFn (fun earlier : Fin (previous.val + 1) =>
      point ⟨earlier.val, by omega⟩) =
    (List.ofFn (fun earlier : Fin previous.val =>
      point ⟨earlier.val, by omega⟩)).concat (point previous.castSucc)
  rw [List.ofFn_succ']
  congr 1

/-- A degree-bounded source polynomial given by chronological partial
restrictions.  The Boolean table supplies only the initial cube sum; no
off-domain endpoint is inferred from its multilinear extension. -/
structure SourcePolynomial (table : Fin 1024 → K) where
  restriction : (round : Fin 10) → List K → K[X]
  degree : ∀ round history, history.length = round.val →
    (restriction round history).natDegree ≤ 27
  initialBoundary :
    (restriction 0 []).eval 0 + (restriction 0 []).eval 1 = ∑ row, table row
  successorBoundary : ∀ (previous : Fin 9) (history : List K) (challenge : K),
    history.length = previous.val →
    (restriction previous.succ (history.concat challenge)).eval 0 +
        (restriction previous.succ (history.concat challenge)).eval 1 =
      (restriction previous.castSucc history).eval challenge

/-- The actual causal messages for one realised challenge path. -/
noncomputable def sourceMessages {table : Fin 1024 → K}
    (source : SourcePolynomial table) (point : Fin 10 → K) : Fin 10 → K[X] :=
  fun round => source.restriction round (sourceHistory point round)

theorem sourceMessages_degree {table : Fin 1024 → K}
    (source : SourcePolynomial table) (point : Fin 10 → K) (round : Fin 10) :
    (sourceMessages source point round).natDegree ≤ 27 := by
  exact source.degree round (sourceHistory point round)
    (sourceHistory_length point round)

/-- Prefix noninterference is a theorem of the constructor: future challenge
coordinates cannot affect a message that has already been fixed. -/
theorem sourceMessages_prefix_independent {table : Fin 1024 → K}
    (source : SourcePolynomial table) (left right : Fin 10 → K)
    (round : Fin 10)
    (same : ∀ coordinate, coordinate.val < round.val →
      left coordinate = right coordinate) :
    sourceMessages source left round = sourceMessages source right round := by
  apply congrArg (source.restriction round)
  unfold sourceHistory
  apply congrArg List.ofFn
  funext earlier
  exact same _ earlier.isLt

/-- The same source polynomial supplies a genuine `ReferenceTrace`; no
terminal claim or callback equality is accepted as an input. -/
noncomputable def sourceReferenceTrace {table : Fin 1024 → K}
    (source : SourcePolynomial table) (point : Fin 10 → K) :
    ReferenceTrace table point where
  messages := sourceMessages source point
  degree := sourceMessages_degree source point
  boundary := by
    intro round
    refine Fin.cases ?_ (fun previous => ?_) round
    · simpa [sourceMessages, sourceHistory, referenceClaim] using
        source.initialBoundary
    · rw [sourceMessages, sourceHistory_succ]
      simpa [sourceMessages, referenceClaim] using
        source.successorBoundary previous
          (sourceHistory point previous.castSucc) (point previous.castSucc)
          (sourceHistory_length point previous.castSucc)

/-- Evaluation of the source polynomial on a complete point.  It is the
evaluation of the final causal restriction, not the table MLE. -/
noncomputable def sourceEvaluation {table : Fin 1024 → K}
    (source : SourcePolynomial table) (point : Fin 10 → K) : K :=
  (sourceMessages source point (Fin.last 9)).eval (point (Fin.last 9))

/-- The constructed honest trace ends at the evaluation of the same source
polynomial.  This follows from the definitions; it is not a structure field. -/
theorem sourceReferenceTrace_terminal {table : Fin 1024 → K}
    (source : SourcePolynomial table) (point : Fin 10 → K) :
    referenceClaim (∑ row, table row) (sourceReferenceTrace source point).messages
      point (Fin.last 10) = sourceEvaluation source point := by
  rfl

#print axioms sourceHistory_succ
#print axioms sourceMessages_degree
#print axioms sourceMessages_prefix_independent
#print axioms sourceReferenceTrace
#print axioms sourceReferenceTrace_terminal
end AspisV8Completion.CausalSourcePolynomialTrace
