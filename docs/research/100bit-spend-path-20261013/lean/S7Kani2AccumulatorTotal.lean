import S7Kani2AccumulatorLoop

/-! Domain-preserving step success makes the actual row driver total.
This is the remaining invariant interface, not a claim that the production
backend has already supplied it. -/
set_option autoImplicit false
namespace S7Kani2AccumulatorLoop
open Aeneas Aeneas.Std Result

/-- Iteration preserves the complete state invariant and is total whenever
each reached step is. The counter bound is checked at each induction step. -/
theorem iterate_total (f : Usize → State → Result State)
    (invariant : Nat → State → Prop) (width : Usize) (n : Nat)
    (j : Usize) (state : State) (hwidth : width.val ≤ 256)
    (remaining : j.val+n=width.val) (initial : invariant j.val state)
    (one : ∀ i s, i.val < width.val → invariant i.val s →
      ∃ t, f i s = ok t ∧ invariant (i.val+1) t) :
    ∃ result, iterate f n j state = ok result ∧ invariant width.val result := by
  induction n generalizing j state with
  | zero => exact ⟨state,rfl,by simpa only [Nat.add_zero] using remaining ▸ initial⟩
  | succ n ih =>
      obtain ⟨nextState,hstep,hInv⟩ := one j state (by omega) initial
      obtain ⟨j1,hj1,hval⟩ := increment j (by omega)
      obtain ⟨result,hr,hfinal⟩ := ih j1 nextState (by omega)
        (by simpa only [hval] using hInv)
      exact ⟨result,by simp only [iterate,hstep,hj1,bind_tc_ok,hr],hfinal⟩

/-- Instantiation for the emitted recurrence. Success is derived from local
step success and preservation, rather than assumed for the whole loop. -/
theorem extracted_loop_total (backend : Backend) (basis : Array U32 256#usize)
    (power : K) (next width j : Usize) (n : Nat) (state : State)
    (invariant : Nat → State → Prop) (hwidth : width.val ≤ 256)
    (remaining : j.val+n=width.val) (initial : invariant j.val state)
    (one : ∀ i s, i.val < width.val → invariant i.val s →
      ∃ t, step backend basis power next width i s = ok t ∧ invariant (i.val+1) t) :
    ∃ result,
      accumulate_rows_owned backend state.1 state.2 basis power next width j = ok result ∧
      invariant width.val result := by
  rw [extracted_loop_composition backend basis power next width j n state hwidth remaining]
  exact iterate_total _ invariant width n j state hwidth remaining initial one

#print axioms iterate_total
#print axioms extracted_loop_total
end S7Kani2AccumulatorLoop
