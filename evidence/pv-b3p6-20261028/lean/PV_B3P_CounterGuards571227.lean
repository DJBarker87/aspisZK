import PV_B3P_PanicPatterns571227
import PV_B3P_IndexRangeFormatting569227
namespace PV_B3P_CounterGuards571227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227
open PV_B3P_PreconditionFormatting569227
set_option autoImplicit false
/-- The numeric projection of the initializer source: a successor can be
committed only after generate/store return normally. Arbitrary intervening
source effects do not add a counter transition. -/
def Initial (i : Usize) : Prop := i = 0#usize
def Commit (length : Usize) (i j : Usize) : Prop :=
  i.val < length.val ∧ j = Usize.wrapping_add i 1#usize

/-- Proved from the zero constructor and each successor, rather than assumed
as a property of the reachable states. Binding this projection to native
regions and every actual caller is a separate source association. -/
theorem prefix_invariant (length i : Usize)
    (reached : Reachable Initial (Commit length) i) : i.val ≤ length.val := by
  apply reachable_guard Initial (Commit length)
    (fun k => k.val ≤ length.val) (fun k => k.val ≤ length.val)
    (fun k initial => by rw [initial]; scalar_tac)
    (fun k next _ edge => by
      rw [edge.2]
      exact (initializer_conditions k length edge.1).2.2)
    (fun _ h => h) i reached

/-- A single guard package for both the emitted IndexRange cursor and every
initializer counter, regardless of values or callback failure behaviour. -/
theorem counter_guards (length i : Usize)
    (reached : Reachable Initial (Commit length) i) (active : i ≠ length) :
    indexGuard ⟨i.val,length.val⟩ ∧
    arithmeticGuard (.add i.val 1 (UScalar.max .Usize)) ∧
    (Usize.wrapping_add i 1#usize).val ≤ length.val := by
  exact index_range_conditions i length (prefix_invariant length i reached) active

theorem index_diagnostic_excluded (length i : Usize)
    (reached : Reachable Initial (Commit length) i) (active : i ≠ length) :
    ¬ diagnostic (indexGuard ⟨i.val,length.val⟩) := by
  intro failed
  exact failed (counter_guards length i reached active).1

theorem add_diagnostic_excluded (length i : Usize)
    (reached : Reachable Initial (Commit length) i) (active : i ≠ length) :
    ¬ diagnostic (arithmeticGuard (.add i.val 1 (UScalar.max .Usize))) := by
  intro failed
  exact failed (counter_guards length i reached active).2.1

/-- Zero/length is the actual numeric shape used by IntoIter's initial alive
range. No external ordered-cursor hypothesis is needed to construct it. -/
def initial_cursor (length : Usize) : PV_B3P_IndexRangeFormatting569227.Cursor length :=
  ⟨⟨0#usize,length⟩,by scalar_tac,by exact Nat.le_refl _⟩

theorem initial_cursor_handler_independent {α β : Type}
    (length : Usize) (assert1 add1 assert2 add2 : Result Unit)
    (step : α → Usize → Result (ControlFlow α β)) (accum : α) :
    PV_B3P_IndexRangeFormatting569227.source assert1 add1 step (initial_cursor length,accum) =
    PV_B3P_IndexRangeFormatting569227.source assert2 add2 step (initial_cursor length,accum) :=
  PV_B3P_IndexRangeFormatting569227.handler_independent _ _ _ _ _ _

/-- ZST slice-next's second arithmetic shape, with its exact nonzero test. -/
theorem subtraction_guard (length : Usize) (nonempty : length ≠ 0#usize) :
    arithmeticGuard (.sub length.val 1) := by
  have nonzero : length.val ≠ 0 := by
    intro equal
    exact nonempty (UScalar.eq_of_val_eq equal)
  change 1 ≤ length.val
  omega

#print axioms prefix_invariant
#print axioms counter_guards
#print axioms index_diagnostic_excluded
#print axioms add_diagnostic_excluded
#print axioms initial_cursor_handler_independent
#print axioms subtraction_guard
end PV_B3P_CounterGuards571227
