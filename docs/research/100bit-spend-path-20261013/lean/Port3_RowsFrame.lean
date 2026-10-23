import Port3_PushFrame

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_RowsFrame
open Aeneas Aeneas.Std Result
open S7Kani2AccumulatorLoop
open Port3_PushFrame

theorem iterate_fields (basis : Array U32 256#usize) (power : K) (next j : Usize)
    (n : Nat) (state after : State) (remaining : j.val+n=64)
    (size : state.2.raw.val.length=64)
    (success : iterate (step S7JoinRowsTrace.backend basis power next 64#usize) n j state = ok after) :
    after.1=state.1 ∧ after.2.raw.val.length=64 ∧ after.2.terms=state.2.terms := by
  induction n generalizing j state with
  | zero =>
    have same := Result.ok.inj success
    subst after
    exact ⟨rfl,size,rfl⟩
  | succ n ih =>
    simp only [iterate] at success
    obtain ⟨mid,hs,success⟩ := bind_success _ _ _ success
    obtain ⟨j1,hj,success⟩ := bind_success _ _ _ success
    obtain ⟨j2,hj2,hv⟩ := increment j (by omega)
    have same : j2=j1 := Result.ok.inj (hj2.symm.trans hj)
    subst j2
    have frame := step_fields basis power next 64#usize j state mid (by omega) hs
    have tail := ih j1 mid (by omega) (frame.2.1.trans size) success
    exact ⟨tail.1.trans frame.1,tail.2.1,tail.2.2.trans frame.2.2⟩

theorem rows_fields (basis : Array U32 256#usize) (power : K) (next : Usize)
    (state after : State) (size : state.2.raw.val.length=64)
    (success : accumulate_rows_owned S7JoinRowsTrace.backend state.1 state.2 basis power next
      64#usize 0#usize = ok after) :
    after.1=state.1 ∧ after.2.raw.val.length=64 ∧ after.2.terms=state.2.terms := by
  rw [extracted_loop_composition S7JoinRowsTrace.backend basis power next 64#usize 0#usize
    64 state (by decide) (by decide)] at success
  exact iterate_fields basis power next 0#usize 64 state after (by decide) size success

#print axioms iterate_fields
#print axioms rows_fields
end AspisR1.Port3_RowsFrame
end
