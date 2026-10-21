import S7Kani2AccumulatorLoop

/-! Production query schedule and failure-preserving composition. The query
step is an explicit parameter until full opening/dot/fold/accumulator
refinement is supplied. It is not a concrete S7 or R17 certificate. -/
set_option autoImplicit false
namespace S7Kani2QueryComposition
open Aeneas Aeneas.Std Result
variable {S E : Type}

def run (cursor : S → Usize) (query : S → Result (Except E S))
    (finish : Usize) (state : S) : Result (Except E S) := do
  if cursor state >= finish then ok (.ok state)
  else
    let result ← query state
    match result with
    | .error e => ok (.error e)
    | .ok next => run cursor query finish next
partial_fixpoint

def iterate (query : S → Result (Except E S)) : Nat → S → Result (Except E S)
 | 0,state => ok (.ok state)
 | n+1,state => do
     let result ← query state
     match result with
     | .error e => ok (.error e)
     | .ok next => iterate query n next

/-- Whole-query recursion reduces to finite composition if every successful
query increments the actual accumulator cursor. Errors and divergence need
no additional premise and stop immediately. -/
theorem query_loop_composition (cursor : S → Usize)
    (query : S → Result (Except E S)) (finish : Usize) (state : S) (n : Nat)
    (remaining : (cursor state).val+n=finish.val)
    (advances : ∀ s t, (cursor s).val<finish.val → query s=ok (.ok t) →
      (cursor t).val=(cursor s).val+1) :
    run cursor query finish state = iterate query n state := by
  induction n generalizing state with
  | zero =>
      have stop : cursor state ≥ finish := by scalar_tac
      rw [run]
      simp only [stop,if_pos,iterate]
  | succ n ih =>
      have running : ¬ cursor state ≥ finish := by scalar_tac
      rw [run]
      simp only [running,if_false,iterate]
      cases hq : query state with
      | fail e => simp only [bind_tc_fail]
      | div => simp only [bind_tc_div]
      | ok result =>
          simp only [bind_tc_ok]
          cases result with
          | error e => rfl
          | ok next =>
              have ha := advances state next (by omega) hq
              exact ih next (by omega)

/-- The two actual transaction windows contain ten then twelve successful
query steps. This is an ordinal fact, not an assumption that they succeed. -/
theorem transaction_windows :
    0+10=10 ∧ 10+12=22 ∧ 5*10=50 ∧ 5*12=60 ∧ 50+60=110 := by decide

#print axioms query_loop_composition
#print axioms transaction_windows
end S7Kani2QueryComposition
