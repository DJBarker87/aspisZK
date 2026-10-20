import AeneasActualRevFoldRefinementV2
import CurrentWideUnrolledRecordPolynomialV1
import CurrentWideReverseRangeFoldModelV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1CurrentWide.Proof

namespace AspisR1CurrentWide.AeneasPolynomialConsumer

private theorem bind_return {α : Type} (r : Result α) :
    Bind.bind r (fun value => Result.ok value) = r := by
  cases r <;> rfl

def currentPolynomialStep (bytes : Slice U8) (x : E)
    (state : E) (index : Nat) : Result E := do
  let product ← field.wide_exact.WideExact.mul state x
  let coefficient ← currentRecordFieldLookupNat bytes index
  field.wide_exact.WideExact.add product coefficient

theorem actual_loop_eq_reverseRangeResult_seven
    {α : Type} (step : α → Nat → Result α) (state : α) :
    AspisR1CurrentWide.RevFoldRefinementV2.actualRfoldLoop 8
      AspisR1CurrentWide.RevFoldRefinementV2.actualInitialRevRange
      step state = reverseRangeResult step 7 state := by
  rw [AspisR1CurrentWide.RevFoldRefinementV2.actual_rfold_loop_zero_seven]
  calc
    AspisR1CurrentWide.RevFoldRefinementV2.foldIndices step
        [6, 5, 4, 3, 2, 1, 0] state =
      Bind.bind (step state 6) (fun s6 =>
      Bind.bind (step s6 5) (fun s5 =>
      Bind.bind (step s5 4) (fun s4 =>
      Bind.bind (step s4 3) (fun s3 =>
      Bind.bind (step s3 2) (fun s2 =>
      Bind.bind (step s2 1) (fun s1 => step s1 0)))))) := by
        simp only [AspisR1CurrentWide.RevFoldRefinementV2.foldIndices,
          bind_return]
    _ = reverseRangeResult step 7 state :=
      (reverseRangeResult_seven step state).symm

private theorem result_bind_assoc {α β γ : Type}
    (r : Result α) (f : α → Result β) (g : β → Result γ) :
    Bind.bind (Bind.bind r f) g =
      Bind.bind r (fun a => Bind.bind (f a) g) := by
  cases r <;> rfl

theorem current_unrolled_eq_reverseRangeResult_seven
    (bytes : Slice U8) (x : E) :
    current_unrolled_record_polynomial bytes x =
      reverseRangeResult (currentPolynomialStep bytes x) 7 currentWideZero := by
  simp only [reverseRangeResult, currentPolynomialStep,
    current_unrolled_record_polynomial, Nat.reduceAdd, result_bind_assoc]

theorem actual_loop_eq_current_unrolled (bytes : Slice U8) (x : E) :
    AspisR1CurrentWide.RevFoldRefinementV2.actualRfoldLoop 8
      AspisR1CurrentWide.RevFoldRefinementV2.actualInitialRevRange
      (currentPolynomialStep bytes x) currentWideZero =
    current_unrolled_record_polynomial bytes x := by
  rw [actual_loop_eq_reverseRangeResult_seven]
  exact (current_unrolled_eq_reverseRangeResult_seven bytes x).symm

theorem actual_loop_success_iff_current_unrolled_success
    (bytes : Slice U8) (x out : E) :
    AspisR1CurrentWide.RevFoldRefinementV2.actualRfoldLoop 8
        AspisR1CurrentWide.RevFoldRefinementV2.actualInitialRevRange
        (currentPolynomialStep bytes x) currentWideZero = .ok out ↔
      current_unrolled_record_polynomial bytes x = .ok out := by
  rw [actual_loop_eq_current_unrolled]

#print axioms actual_loop_eq_current_unrolled
#print axioms actual_loop_eq_reverseRangeResult_seven
#print axioms actual_loop_success_iff_current_unrolled_success

end AspisR1CurrentWide.AeneasPolynomialConsumer
