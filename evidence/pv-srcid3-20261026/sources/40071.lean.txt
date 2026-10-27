import R1Z.PV_Src_PortInternalStep

/-! Symbolic recurrence for all fifteen source internal-linear writes.
Each step is named and scalar; this never unfolds a concrete hash recurrence. -/
set_option autoImplicit false
namespace R1Z.PV_Src_PortInternalLoop
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort PV_Src_PortInternalStep

def steps (n : Nat) (index : Usize) (state : State) (full : U64) : State :=
  match n with
  | 0 => state
  | n+1 => steps n (Usize.wrapping_add index 1#usize)
      (state.set index (cell state full index)) full

theorem loop (n : Nat) (iter : core.ops.range.Range Usize) (state : State)
    (full : U64) (lo : 1 ≤ iter.start.val) (count : iter.start.val+n=16)
    (hend : iter.end.val=16) :
    poseidon2.internal_linear_lazy_loop iter state full =
      ok (steps n iter.start state full) := by
  induction n generalizing iter state with
  | zero =>
    rw [poseidon2.internal_linear_lazy_loop,BuilderBankRange.next_none iter (by omega)]
    rfl
  | succ n ih =>
    obtain ⟨after,hn,ha,he⟩ := BuilderBankRange.next_some iter (by omega)
    rw [PV_Src_PortInternalStep.step iter after state full iter.start lo (by omega) hn]
    rw [ih after _ (by rw [ha];omega) (by rw [ha];omega) (by rw [he];exact hend)]
    simp only [steps]
    congr 2
    apply UScalar.eq_of_val_eq
    rw [ha,BuilderRecordsArray.next_val iter.start (by omega)]

theorem full_loop (state : State) (full : U64) :
    poseidon2.internal_linear_lazy_loop {start := 1#usize, «end» := 16#usize}
      state full = ok (steps 15 1#usize state full) :=
  loop 15 _ state full (by decide) (by decide) (by decide)

#print axioms loop
#print axioms full_loop
end R1Z.PV_Src_PortInternalLoop
