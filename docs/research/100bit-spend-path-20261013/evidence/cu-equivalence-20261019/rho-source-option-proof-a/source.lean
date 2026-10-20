import AspisR1RhoSourceOption.Funs
import CuSavingsRhoOptionLoans
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoSourceOption
open Aeneas Aeneas.Std Result
open CuSavingsRhoOptionLoans
abbrev BW := AspisR1RhoSourceOption.BatchedWeights

def inner (original replacement : Option BW) : Option BW :=
  match original with
  | none => none
  | some _ => replacement

theorem source_outcome (original : Option BW) :
    AspisR1RhoSourceOption.source_reborrow original =
      .ok (original,restore original,inner original) := by
  cases original with
  | none => rfl
  | some x =>
    simp only [AspisR1RhoSourceOption.source_reborrow,restore,inner]
    congr 2
    funext replacement
    cases replacement <;> rfl

theorem source_some (value replacement : BW) :
    (do let (view,outer,inner) ← AspisR1RhoSourceOption.source_reborrow (some value)
        pure (view,outer (some replacement),inner (some replacement))) =
      (.ok (some value,some replacement,some replacement) : Result _) := rfl

theorem source_none (replacement : Option BW) :
    (do let (view,outer,inner) ← AspisR1RhoSourceOption.source_reborrow none
        pure (view,outer replacement,inner replacement)) =
      (.ok (none,none,none) : Result (Option BW × Option BW × Option BW)) := rfl

#print axioms source_outcome
#print axioms source_some
#print axioms source_none
end AspisR1.CuSavingsRhoSourceOption
