import BooleanSuffixSourceConstructor

/-! Instantiation of the generic Boolean-suffix constructor for one literal
selected range lane.

The only semantic work left here is local: the exact three-row range selector
times one fixed trace-column opening Booleanity slice, its evaluation identity,
and its degree-three bound. `BooleanSuffixSourceConstructor` supplies the ten
causal messages and proves every boundary. -/
set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.SelectedRangeLaneSourcePolynomial
open Polynomial
open scoped BigOperators
open AspisV8Completion.CausalSourcePolynomialTrace
open AspisV8Completion.SelectedRangeLaneCoordinateSlice
open AspisV8Completion.BooleanSuffixSourceConstructor

variable {K : Type*} [Field K] [DecidableEq K]

noncomputable def slices (table : Fin 1024 → K) : CoordinateSlices (K := K) where
  value := rangeLaneValue table
  slice := rangeLaneSlice table
  degree := rangeLaneSlice_degree_le_source_bound table
  eval_at := rangeLaneSlice_eval_at table

noncomputable def rangeLaneBooleanTable (table : Fin 1024 → K) : Fin 1024 → K :=
  booleanTable (slices table)

/-- A chronological source object for the literal selected range lane. The
committed trace-column table is fixed before any source challenge. -/
noncomputable def source (table : Fin 1024 → K) :
    SourcePolynomial (rangeLaneBooleanTable table) :=
  BooleanSuffixSourceConstructor.source (slices table)

theorem source_degree (table : Fin 1024 → K) (round : Fin 10)
    (history : List K) (length : history.length = round.val) :
    ((source table).restriction round history).natDegree ≤ 27 :=
  (source table).degree round history length

theorem source_initial_boundary (table : Fin 1024 → K) :
    ((source table).restriction 0 []).eval 0 +
        ((source table).restriction 0 []).eval 1 =
      ∑ row, rangeLaneBooleanTable table row :=
  (source table).initialBoundary

theorem source_successor_boundary (table : Fin 1024 → K)
    (previous : Fin 9) (history : List K) (challenge : K)
    (length : history.length = previous.val) :
    ((source table).restriction previous.succ (history.concat challenge)).eval 0 +
        ((source table).restriction previous.succ (history.concat challenge)).eval 1 =
      ((source table).restriction previous.castSucc history).eval challenge :=
  (source table).successorBoundary previous history challenge length

#print axioms slices
#print axioms source
#print axioms source_degree
#print axioms source_initial_boundary
#print axioms source_successor_boundary
end AspisV8Completion.SelectedRangeLaneSourcePolynomial
