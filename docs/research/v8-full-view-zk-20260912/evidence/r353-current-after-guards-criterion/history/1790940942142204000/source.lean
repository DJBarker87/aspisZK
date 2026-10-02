import AspisV8R19.R350AfterGuardsExecution
import AspisV8R19.R341PrefixNonzero

/-! Exact selected after-guards success/failure criterion. This does not model
or prove the original zero-detection iterator guard. -/
set_option autoImplicit false
namespace AspisV8R19.R353AfterGuardsCriterion
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase
open AspisV8R19.ComplexBaseExecution (encodeBase)
open AspisV8R19.R332PrefixInitializationSelectors
open AspisV8R19.R350AfterGuardsExecution
open AspisV8R19.R341PrefixNonzero
open AspisR346AfterGuardsRaw (selectedAfterGuards)
noncomputable section

theorem after_guards_succeeds_iff
    (xs ys : Slice U32) (f g : Nat → M31Exact)
    (hx : 0 < xs.val.length) (hy : 0 < ys.val.length)
    (hf : ∀ j, j < xs.val.length → xs.val[j]? = some (encodeBase (f j)))
    (hg : ∀ j, j < ys.val.length → ys.val[j]? = some (encodeBase (g j))) :
    (∃ ox oy : alloc.vec.Vec U32,
      selectedAfterGuards xs ys = .ok (core.result.Result.Ok (ox, oy))) ↔
      (∀ j, j < xs.val.length → f j ≠ 0) ∧
      (∀ j, j < ys.val.length → g j ≠ 0) := by
  have hrun := after_guards_complete xs ys f g hx hy hf hg
  have hcriterion := initialized_pair_total_ne_zero_iff f g
    xs.val.length ys.val.length hx hy
  constructor
  · rintro ⟨ox, oy, hok⟩
    apply hcriterion.mp
    intro hz
    simp only [if_pos hz] at hrun
    rw [hrun] at hok
    cases hok
  · intro hn
    have hz := hcriterion.mpr hn
    rw [hrun]
    simp only [if_neg hz]
    exact ⟨_, _, rfl⟩

theorem after_guards_assertion_failure_iff
    (xs ys : Slice U32) (f g : Nat → M31Exact)
    (hx : 0 < xs.val.length) (hy : 0 < ys.val.length)
    (hf : ∀ j, j < xs.val.length → xs.val[j]? = some (encodeBase (f j)))
    (hg : ∀ j, j < ys.val.length → ys.val[j]? = some (encodeBase (g j))) :
    selectedAfterGuards xs ys = .fail .assertionFailure ↔
      ¬ ((∀ j, j < xs.val.length → f j ≠ 0) ∧
         (∀ j, j < ys.val.length → g j ≠ 0)) := by
  have hcriterion := initialized_pair_total_ne_zero_iff f g
    xs.val.length ys.val.length hx hy
  have hziff : sourcePrefixValue f (xs.val.length - 1) *
      sourcePrefixValue g (ys.val.length - 1) = 0 ↔
      ¬ ((∀ j, j < xs.val.length → f j ≠ 0) ∧
         (∀ j, j < ys.val.length → g j ≠ 0)) := by
    simpa only [not_not] using not_congr hcriterion
  rw [← hziff, after_guards_complete xs ys f g hx hy hf hg]
  by_cases hz : sourcePrefixValue f (xs.val.length - 1) *
      sourcePrefixValue g (ys.val.length - 1) = 0
  · simp only [if_pos hz, hz, iff_self]
  · simp only [if_neg hz, reduceCtorEq, hz, iff_self]

theorem after_guards_failure_has_zero_iff
    (xs ys : Slice U32) (f g : Nat → M31Exact)
    (hx : 0 < xs.val.length) (hy : 0 < ys.val.length)
    (hf : ∀ j, j < xs.val.length → xs.val[j]? = some (encodeBase (f j)))
    (hg : ∀ j, j < ys.val.length → ys.val[j]? = some (encodeBase (g j))) :
    selectedAfterGuards xs ys = .fail .assertionFailure ↔
      (∃ j, j < xs.val.length ∧ f j = 0) ∨
      (∃ j, j < ys.val.length ∧ g j = 0) := by
  classical
  rw [after_guards_assertion_failure_iff xs ys f g hx hy hf hg]
  simp only [not_and_or, not_forall, Classical.not_imp, not_not]

#print axioms after_guards_succeeds_iff
#print axioms after_guards_assertion_failure_iff
#print axioms after_guards_failure_has_zero_iff
end
end AspisV8R19.R353AfterGuardsCriterion
