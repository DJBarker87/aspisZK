import SelectedSemanticPackedLiteral

/-! First exact source-polynomial producer for the selected semantic path.

The literal range lane in `semantic_packed` contains `z*z-z`.  Unlike the
Boolean writer, this polynomial remains visible off the Boolean cube.  This
leaf constructs all ten chronological partial-sum messages for that actual
source factor and packages them as `CausalSourcePolynomialTrace.SourcePolynomial`.
The terminal evaluation is then proved to be the same `z*z-z` expression at
the sampled point; it is not inferred from the zero Boolean table.

The surrounding range selector, openings-to-source-variable refinement, and
the other 93 semantic outputs remain to be composed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 500
set_option maxHeartbeats 500000

namespace AspisV8Completion.SelectedBooleanitySourcePolynomial
open Polynomial
open AspisV6TranscriptRelationGrammar
open AspisV8.SelectedCompactSemanticRepair
open AspisV8.SelectedSemanticLaneAggregation
open AspisV8Completion.CausalSourcePolynomialTrace
open AspisV8Completion.SourcePolynomialEndpointObstruction

variable {K : Type*} [Field K] [DecidableEq K]

def booleanityValue (z : K) : K := z * (z - 1)

noncomputable def booleanityPolynomial : K[X] := X * (X - 1)

theorem booleanityPolynomial_eval (z : K) :
    booleanityPolynomial.eval z = booleanityValue z := by
  simp [booleanityPolynomial, booleanityValue]

/-- At round zero, sum over the remaining nine Boolean coordinates.  Once
coordinate zero is fixed, subsequent messages are constants with the exact
remaining-cube multiplicity. -/
noncomputable def restriction (round : Fin 10) (history : List K) : K[X] :=
  if round.val = 0 then
    C ((2 : K) ^ 9) * booleanityPolynomial
  else
    C ((2 : K) ^ (9 - round.val) * booleanityValue (history.headD 0))

theorem restriction_degree (round : Fin 10) (history : List K) :
    (restriction round history).natDegree ≤ 27 := by
  unfold restriction
  split
  · refine (natDegree_C_mul_le ((2 : K) ^ 9) booleanityPolynomial).trans ?_
    have polyDegree : (booleanityPolynomial (K := K)).natDegree ≤ 2 := by
      unfold booleanityPolynomial
      calc
        (X * (X - 1) : K[X]).natDegree ≤
            X.natDegree + (X - 1 : K[X]).natDegree := natDegree_mul_le
        _ = 1 + 1 := by
          rw [natDegree_X, show (X - 1 : K[X]) = X - C 1 by simp,
            natDegree_X_sub_C]
        _ = 2 := rfl
    exact polyDegree.trans (by omega)
  · rw [natDegree_C]
    omega

theorem restriction_initial_boundary :
    (restriction (K := K) 0 []).eval 0 +
      (restriction (K := K) 0 []).eval 1 =
        ∑ _row : Fin 1024, (zeroBooleanTable : Fin 1024 → K) _row := by
  simp [restriction, booleanityPolynomial_eval, booleanityValue, zeroBooleanTable]

theorem restriction_successor_boundary (previous : Fin 9)
    (history : List K) (challenge : K) (length : history.length = previous.val) :
    (restriction previous.succ (history.concat challenge)).eval 0 +
        (restriction previous.succ (history.concat challenge)).eval 1 =
      (restriction previous.castSucc history).eval challenge := by
  fin_cases previous <;> cases history <;>
    simp_all [restriction, booleanityPolynomial_eval, booleanityValue, pow_succ] <;> ring

/-- A genuine causal source object for the literal Booleanity factor. -/
noncomputable def source : SourcePolynomial
    (zeroBooleanTable : Fin 1024 → K) where
  restriction := restriction
  degree := fun round history _ => restriction_degree round history
  initialBoundary := restriction_initial_boundary
  successorBoundary := restriction_successor_boundary

theorem source_evaluation_eq_booleanity (point : Fin 10 → K) :
    sourceEvaluation (source (K := K)) point = booleanityValue (point 0) := by
  simp [sourceEvaluation, sourceMessages, source, restriction, sourceHistory,
    booleanityValue]

/-- This constructed trace reaches the actual off-domain source factor. -/
theorem source_trace_terminal (point : Fin 10 → K) :
    referenceClaim 0 (sourceReferenceTrace (source (K := K)) point).messages
        point (Fin.last 10) = booleanityValue (point 0) := by
  rw [show (0 : K) = ∑ row, (zeroBooleanTable : Fin 1024 → K) row by
    simp [zeroBooleanTable]]
  rw [sourceReferenceTrace_terminal, source_evaluation_eq_booleanity]

theorem source_boolean_restriction (row : Fin 1024) :
    booleanityValue ((booleanTracePoint row : Fin 10 → K) 0) = 0 := by
  simpa [booleanityValue, firstCoordinateBooleanity] using
    (firstCoordinateBooleanity_booleanRow (K := K) row)

#print axioms restriction_degree
#print axioms restriction_initial_boundary
#print axioms restriction_successor_boundary
#print axioms source
#print axioms source_evaluation_eq_booleanity
#print axioms source_trace_terminal
#print axioms source_boolean_restriction
end AspisV8Completion.SelectedBooleanitySourcePolynomial
