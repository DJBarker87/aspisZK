import R1Z.PV_RW_NativeForBound
import R1Z.PV_RW_NativeCursor
import R1Z.PV_RW_CursorLoop
set_option autoImplicit false
namespace R1Z.PV_RW_NativeForModel
open Aeneas Aeneas.Std Result
open PV_RW_NativeForSource

theorem bounded {S : Type} (step : U32 → S → Result S) (fuel : Nat) (iterator : Iter) (state : S) :
    PV_RW_ResultOutcome.toOutcome (PV_RW_NativeForSource.bounded step fuel iterator state)=
      PV_RW_CursorLoop.bounded (fun value state => PV_RW_ResultOutcome.toOutcome (step value state))
        fuel (PV_RW_NativeCursor.cursor iterator) state := by
  induction fuel generalizing iterator state with
  | zero => rfl
  | succ fuel ih =>
    rcases iterator with ⟨values,i⟩
    by_cases active : i<values.val.length
    · rw [bounded_some step values i active]
      rw [PV_RW_CursorLoop.bounded,PV_RW_Cursor.some_step _ active]
      rw [PV_RW_ResultOutcome.bind]
      apply PV_RW_Outcome.congr
      intro next
      exact ih (⟨values,i+1⟩ : Iter) next
    · have stopped : values.val.length ≤ i := by omega
      rw [bounded_none step values i stopped]
      rw [PV_RW_CursorLoop.bounded,PV_RW_Cursor.none_step _ stopped]
      rfl

theorem run {S : Type} (step : U32 → S → Result S) (iterator : Iter) (state : S) :
    PV_RW_ResultOutcome.toOutcome (PV_RW_NativeForSource.run step iterator state)=
      PV_RW_CursorLoop.listRun (fun value state => PV_RW_ResultOutcome.toOutcome (step value state))
        (PV_RW_Cursor.remaining (PV_RW_NativeCursor.cursor iterator)) state := by
  rcases iterator with ⟨values,i⟩
  rw [PV_RW_NativeForBound.exact_fuel]
  rw [bounded]
  apply PV_RW_CursorLoop.complete
  simp only [PV_RW_Cursor.remaining,PV_RW_NativeCursor.cursor,List.length_drop]
  omega

-- Per-step source agreement gives complete Result agreement, including all
-- failed/divergent executions. The loop's output equation is not a premise.
theorem congr {S : Type} (left right : U32 → S → Result S)
    (same : ∀ value state, left value state=right value state) (iterator : Iter) (state : S) :
    PV_RW_NativeForSource.run left iterator state=PV_RW_NativeForSource.run right iterator state := by
  apply PV_RW_ResultOutcome.injective
  rw [run,run]
  apply PV_RW_CursorLoop.congr
  intro value state
  exact congrArg PV_RW_ResultOutcome.toOutcome (same value state)
#print axioms bounded
#print axioms run
#print axioms congr
end R1Z.PV_RW_NativeForModel
