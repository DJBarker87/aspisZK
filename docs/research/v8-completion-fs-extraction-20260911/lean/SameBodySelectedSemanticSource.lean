import SameBodyAssembly
import SelectedConcreteTerminal

/-! A small same-body producer for the two value bindings left explicit by
`SelectedConcreteTerminal`.

The initial mask claim is written into field zero before the relation strategy
is entered.  The strategy still fixes response zero before `alpha`, the final
vector before queries, and each later response before its own challenge via
`SameBodyRelation.produce`; no recovered tuple is supplied to a later stage.

The terminal callback is executed only after the ten semantic challenges and
the 84 selected point claims have been projected from that same word.  Success
of that execution proves equality with the callback result.  Identifying the
actual selected Rust callback result with the fixed-table reference value is
left as one direct source-refinement equality, rather than hidden in a renamed
acceptance predicate.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000
namespace AspisV8Completion.SameBodySelectedSemanticSource
open scoped BigOperators
open AspisV6AcceptedPathObligations
open AspisV8.SelectedCompactSemanticRepair
open AspisV8Completion.SameBodyRelation

variable {K Schedule : Type*} [Field K] [DecidableEq K]

/-- The source-produced semantic prefix.  Only field zero is changed; all
other pre-relation fields retain their independently produced values. -/
def earlyWithMask (mask : Fin 1024 → K) (early : Fin 417 → K) : Fin 417 → K :=
  fun i => if i.val = 0 then ∑ row, mask row else early i

/-- One complete same-body serialization.  Its dependency types retain the
legal fixing points of all four compact relation responses and `final256`. -/
def sourceWord (mask : Fin 1024 → K) (early : Fin 417 → K)
    (strategy : Strategy K Schedule) (tau alpha : K) (queries : Schedule)
    (rho : K) (coins : Fin 3 → K) : Word K :=
  produce (earlyWithMask mask early) strategy tau alpha queries rho coins

/-- Projection of the semantic fields consumed before OOD and relation work.
The unused tail of `FixedFieldView` is deliberately inherited from `rest`;
none of it can affect `semanticTerminalClaim`. -/
def semanticFieldsFromWord (word : Word K) (rest : FixedFieldView K) : FixedFieldView K where
  initialClaim := word 0
  semanticSent := fun round sent => word ⟨1 + 27 * round.val + sent.val, by omega⟩
  pointClaim := fun row column => word ⟨271 + 29 * row.val + column.val, by omega⟩
  inactiveClaim := rest.inactiveClaim
  oodValue := rest.oodValue
  relationSent := rest.relationSent
  finalCoefficient := rest.finalCoefficient

@[simp] theorem sourceWord_initial_mask (mask : Fin 1024 → K)
    (early : Fin 417 → K) (strategy : Strategy K Schedule)
    (tau alpha : K) (queries : Schedule) (rho : K) (coins : Fin 3 → K) :
    sourceWord mask early strategy tau alpha queries rho coins 0 = ∑ row, mask row := by
  simp [sourceWord, produce, assembled_early, earlyWithMask]

@[simp] theorem semanticFields_sourceWord_mask_bound (mask : Fin 1024 → K)
    (early : Fin 417 → K) (strategy : Strategy K Schedule)
    (tau alpha : K) (queries : Schedule) (rho : K) (coins : Fin 3 → K)
    (rest : FixedFieldView K) :
    (semanticFieldsFromWord
      (sourceWord mask early strategy tau alpha queries rho coins) rest).initialClaim =
        ∑ row, mask row := by
  exact sourceWord_initial_mask mask early strategy tau alpha queries rho coins

/-- Shape of the selected source callback.  It receives only the 84 point
claims visible to the Rust semantic terminal and the already sampled point.
Validation errors are represented by `none`. -/
abbrev SelectedTerminalCallback (K : Type*) :=
  (Fin 3 → Fin 28 → K) → (Fin 10 → K) → Option K

/-- Source-order terminal execution: project the point claims, run the
selected callback, then compare its returned value with the carried compact
sumcheck claim. -/
def runSelectedTerminal (callback : SelectedTerminalCallback K)
    (fields : FixedFieldView K) (point : Fin 10 → K) : Option K := do
  let computed ← callback (terminalProjection fields.pointClaim) point
  if semanticTerminalClaim fields point = computed then some computed else none

theorem runSelectedTerminal_success
    (callback : SelectedTerminalCallback K) (fields : FixedFieldView K)
    (point : Fin 10 → K) (computed : K)
    (success : runSelectedTerminal callback fields point = some computed) :
    callback (terminalProjection fields.pointClaim) point = some computed ∧
      semanticTerminalClaim fields point = computed := by
  simp only [runSelectedTerminal] at success
  split at success
  · contradiction
  next value callbackRun =>
    split at success
    next equal =>
      have result := Option.some.inj success
      subst computed
      exact ⟨callbackRun, equal⟩
    next unequal => contradiction

/-- The two exact bindings consumed by `SelectedConcreteTerminal`.  The
callback equality is the remaining selected-terminal Rust/refinement fact:
it states what the independently executed callback returned on the actual
same-body point claims.  Terminal success itself is obtained from
`runSelectedTerminal`, not assumed through another predicate. -/
theorem source_execution_constructs_selected_bindings
    (mask : Fin 1024 → K) (early : Fin 417 → K)
    (strategy : Strategy K Schedule) (tau alpha : K) (queries : Schedule)
    (rho : K) (coins : Fin 3 → K) (rest : FixedFieldView K)
    (point : Fin 10 → K) (callback : SelectedTerminalCallback K)
    {table : Fin 1024 → K} (reference : ReferenceTrace table point)
    (computed : K)
    (success : runSelectedTerminal callback
      (semanticFieldsFromWord
        (sourceWord mask early strategy tau alpha queries rho coins) rest)
      point = some computed)
    (callbackExact : callback
      (terminalProjection
        (semanticFieldsFromWord
          (sourceWord mask early strategy tau alpha queries rho coins) rest).pointClaim)
      point = some
        (referenceClaim (∑ row, table row) reference.messages point (Fin.last 10))) :
    let fields := semanticFieldsFromWord
      (sourceWord mask early strategy tau alpha queries rho coins) rest
    fields.initialClaim = ∑ row, mask row ∧
      semanticTerminalClaim fields point =
        referenceClaim (∑ row, table row) reference.messages point (Fin.last 10) := by
  dsimp only
  have result := runSelectedTerminal_success callback
    (semanticFieldsFromWord
      (sourceWord mask early strategy tau alpha queries rho coins) rest)
    point computed success
  have computedExact : computed =
      referenceClaim (∑ row, table row) reference.messages point (Fin.last 10) := by
    exact Option.some.inj (result.1.symm.trans callbackExact)
  exact ⟨semanticFields_sourceWord_mask_bound mask early strategy tau alpha queries rho coins rest,
    result.2.trans computedExact⟩

section Concrete
open AspisV5ComponentCQM31TowerExact
open AspisV8.SelectedSemanticRows AspisV8.SelectedSemanticTransfer
open AspisV8.SelectedEarlyC1Amounts AspisV8.EarlyC1LateProjection
open AspisV8.EarlyC1CopyCollision AspisV8.SelectedSemanticLaneAggregation
open AspisV8.SelectedSemanticHelperAggregation
open AspisV8.SelectedSemanticTerminalAlternative
open AspisV8.SelectedConcreteRowLanes
open AspisV8.SelectedConcreteTerminal
noncomputable section
abbrev Q := QM31Exact

/-- Direct handoff to the concrete selected terminal.  Both unmatched-value
branches are discharged by the source execution above, while `RepairHit`
remains the sole semantic-sumcheck exception.  `FollowsPlan` is deliberately
still required: a final body and reference record do not prove causal message
fixing. -/
theorem source_execution_constructs_residuals_or_repair
    (T M S : Finset Q) (rc : RoundConstants) (pub : Public)
    (tuple : Fin 29 → Fin 1024 → Q) (lambda chi : Q)
    (active mask : Fin 1024 → Q) (theta : Q)
    (equalityPoint : Fin 10 → Q) (mu eta : Q)
    (thetaInside : theta ∈ T) (muInside : mu ∈ M) (etaNonzero : eta ≠ 0)
    (early : Fin 417 → Q) (strategy : Strategy Q Schedule)
    (tau relationAlpha : Q) (queries : Schedule) (rho : Q)
    (relationCoins : Fin 3 → Q) (rest : FixedFieldView Q)
    (point : Fin 10 → Q) (callback : SelectedTerminalCallback Q)
    (reference : ReferenceTrace
      (maskedTable eta
        (realTable (tupleLanes rc pub tuple lambda chi) (tuple 26) active
          theta equalityPoint mu) mask) point)
    (plan : Plan Q)
    (causal : FollowsPlan
      (semanticFieldsFromWord
        (sourceWord mask early strategy tau relationAlpha queries rho relationCoins) rest)
      point reference plan)
    (inside : ∀ round, point round ∈ S)
    (computed : Q)
    (success : runSelectedTerminal callback
      (semanticFieldsFromWord
        (sourceWord mask early strategy tau relationAlpha queries rho relationCoins) rest)
      point = some computed)
    (callbackExact : callback
      (terminalProjection
        (semanticFieldsFromWord
          (sourceWord mask early strategy tau relationAlpha queries rho relationCoins)
          rest).pointClaim)
      point = some
        (referenceClaim
          (∑ row, maskedTable eta
            (realTable (tupleLanes rc pub tuple lambda chi) (tuple 26) active
              theta equalityPoint mu) mask row)
          reference.messages point (Fin.last 10))) :
    ConcreteOutcome T M rc pub tuple lambda chi active theta equalityPoint mu ∨
      RepairHit S plan point := by
  have bindings := source_execution_constructs_selected_bindings mask early strategy
    tau relationAlpha queries rho relationCoins rest point callback reference computed
    success callbackExact
  exact bound_terminal_constructs_residuals_or_named_exceptions
    T M S rc pub tuple lambda chi
    (semanticFieldsFromWord
      (sourceWord mask early strategy tau relationAlpha queries rho relationCoins) rest)
    point active mask theta equalityPoint mu eta
    thetaInside muInside etaNonzero reference plan causal inside bindings.1 bindings.2

end
end Concrete

#print source_execution_constructs_selected_bindings
#print source_execution_constructs_residuals_or_repair
#print axioms sourceWord_initial_mask
#print axioms runSelectedTerminal_success
#print axioms source_execution_constructs_selected_bindings
#print axioms source_execution_constructs_residuals_or_repair
end AspisV8Completion.SameBodySelectedSemanticSource
