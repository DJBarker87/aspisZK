import CurrentWideUnrolledRecordPolynomialV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1CurrentWide.Proof

/-- The recursive operational model of visiting the half-open range
    `0 .. n` from its back: the next callback receives `n - 1`, then the
    remaining prefix is processed. This is a finite-index model, not a proof
    about Rust's library implementation. -/
def reverseRangeResult {α : Type} (step : α → Nat → Result α) :
    Nat → α → Result α
  | 0, state => .ok state
  | 1, state => step state 0
  | n + 2, state => do
      let next ← step state (n + 1)
      reverseRangeResult step (n + 1) next

theorem reverseRangeResult_seven {α : Type}
    (step : α → Nat → Result α) (state : α) :
    reverseRangeResult step 7 state =
      Bind.bind (step state 6) (fun s6 =>
      Bind.bind (step s6 5) (fun s5 =>
      Bind.bind (step s5 4) (fun s4 =>
      Bind.bind (step s4 3) (fun s3 =>
      Bind.bind (step s3 2) (fun s2 =>
      Bind.bind (step s2 1) (fun s1 =>
        step s1 0)))))) := by
  simp only [reverseRangeResult]

private def currentPolynomialStep (bytes : Slice U8) (x : E)
    (state : E) (index : Nat) : Result E := do
  let product ← field.wide_exact.WideExact.mul state x
  let coefficient ← currentRecordFieldLookupNat bytes index
  field.wide_exact.WideExact.add product coefficient

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

theorem current_unrolled_success_iff_reverseRange_success
    (bytes : Slice U8) (x out : E) :
    current_unrolled_record_polynomial bytes x = .ok out ↔
      reverseRangeResult (currentPolynomialStep bytes x) 7 currentWideZero =
        .ok out := by
  rw [current_unrolled_eq_reverseRangeResult_seven]

#print axioms reverseRangeResult_seven
#print axioms current_unrolled_eq_reverseRangeResult_seven
#print axioms current_unrolled_success_iff_reverseRange_success

end AspisR1CurrentWide.Proof
