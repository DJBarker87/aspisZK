import SameBodySelectedSemanticSource

/-! Exact interface left between the selected Rust semantic callback and the
frozen compact-sumcheck model.

The Rust callback computes the selected masked terminal at the sampled point.
The existing `ReferenceTrace` stores only degree and adjacent-boundary facts;
it does not say that its last evaluation is the multilinear evaluation of its
table.  The construction below demonstrates that omission: at the all-zero
point, a valid reference trace can be made to finish at any requested scalar.

The final theorem therefore factors `callbackExact` into exactly two direct
equalities: literal callback-to-table-MLE refinement and reference-endpoint
authenticity.  Neither equality is called acceptance or assumed by the
same-body runner.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000
namespace AspisV8Completion.SelectedSemanticCallbackGap
open scoped BigOperators
open Polynomial
open AspisV5AcceptedTerminalResidualExtraction
open AspisV6AcceptedPathObligations
open AspisV8.SelectedCompactSemanticRepair
open AspisV8Completion.SameBodySelectedSemanticSource

variable {K : Type*} [Field K] [DecidableEq K]

def zeroPoint : Fin 10 → K := fun _ => 0

/-- Round zero changes the table sum to `target`; every later round preserves
`target`.  Each polynomial is fixed before its own all-zero challenge. -/
noncomputable def arbitraryTerminalMessage
    (initial target : K) (round : Fin 10) : K[X] :=
  if round.val = 0 then
    C target + C (initial - 2 * target) * X
  else
    C target - C target * X

theorem arbitraryTerminalMessage_degree
    (initial target : K) (round : Fin 10) :
    (arbitraryTerminalMessage initial target round).natDegree ≤ 27 := by
  unfold arbitraryTerminalMessage
  split
  · apply (natDegree_add_le _ _).trans
    exact max_le (by simp) ((natDegree_mul_le _ _).trans (by simp))
  · apply (natDegree_sub_le _ _).trans
    exact max_le (by simp) ((natDegree_mul_le _ _).trans (by simp))

@[simp] theorem arbitraryTerminalMessage_zero
    (initial target : K) (round : Fin 10) :
    (arbitraryTerminalMessage initial target round).eval 0 = target := by
  unfold arbitraryTerminalMessage
  split <;> simp

theorem arbitraryTerminalMessage_boundary
    (initial target : K) (round : Fin 10) :
    (arbitraryTerminalMessage initial target round).eval 0 +
      (arbitraryTerminalMessage initial target round).eval 1 =
        if round.val = 0 then initial else target := by
  unfold arbitraryTerminalMessage
  split <;> simp <;> ring

/-- `ReferenceTrace` alone does not authenticate the table evaluation: its
terminal can be an arbitrary scalar even while every degree and boundary
field is satisfied. -/
noncomputable def arbitraryTerminalTrace
    (table : Fin 1024 → K) (target : K) : ReferenceTrace table zeroPoint where
  messages := arbitraryTerminalMessage (∑ row, table row) target
  degree := arbitraryTerminalMessage_degree _ target
  boundary := by
    intro round
    fin_cases round <;>
      simp [arbitraryTerminalMessage, referenceClaim, zeroPoint] <;> ring

@[simp] theorem arbitraryTerminalTrace_final
    (table : Fin 1024 → K) (target : K) :
    referenceClaim (∑ row, table row) (arbitraryTerminalTrace table target).messages
      zeroPoint (Fin.last 10) = target := by
  simp [referenceClaim, arbitraryTerminalTrace, zeroPoint]

/-- The exact value the frozen Boolean-table model assigns to the selected
masked callback.  Proving that the literal pair-forest Rust evaluator returns
this value requires its complete selector/semantic/Copy/mask refinement. -/
noncomputable def fixedTableTerminal
    (table : Fin 1024 → K) (point : Fin 10 → K) : K :=
  tableMLEValue point table

/-- Smallest non-circular producer of the direct `callbackExact` equality.
The first premise is the literal selected Rust callback refinement on the
actual 84 same-body claims.  The second is the missing fixed-oracle trace
endpoint theorem. -/
theorem callback_exact_of_table_terminal
    (callback : SelectedTerminalCallback K) (fields : FixedFieldView K)
    (point : Fin 10 → K) {table : Fin 1024 → K}
    (reference : ReferenceTrace table point)
    (callbackReturnsTable : callback (terminalProjection fields.pointClaim) point =
      some (fixedTableTerminal table point))
    (referenceEndsAtTable :
      referenceClaim (∑ row, table row) reference.messages point (Fin.last 10) =
        fixedTableTerminal table point) :
    callback (terminalProjection fields.pointClaim) point = some
      (referenceClaim (∑ row, table row) reference.messages point (Fin.last 10)) := by
  rw [referenceEndsAtTable]
  exact callbackReturnsTable

#print arbitraryTerminalTrace_final
#print callback_exact_of_table_terminal
#print axioms arbitraryTerminalMessage_degree
#print axioms arbitraryTerminalTrace
#print axioms arbitraryTerminalTrace_final
#print axioms callback_exact_of_table_terminal
end AspisV8Completion.SelectedSemanticCallbackGap
