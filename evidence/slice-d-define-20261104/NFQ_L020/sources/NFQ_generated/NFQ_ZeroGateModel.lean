import NFQ_ZeroPrimitives
set_option autoImplicit false
noncomputable section
namespace NFQ_ZeroGateModel
open Aeneas Aeneas.Std Result ControlFlow
open _root_.AdapterRw

theorem reject_at (bytes : Slice U8) (i : Usize) (value : U8)
    (inside : i.val < bytes.val.length)
    (read : bytes.val[i.val]? = some value) (nonzero : value ≠ 0#u8) :
    r1_pool_adapter.owned.require_zero_loop bytes i =
      ok (some (.Err solana_program_error.ProgramError.AccountAlreadyInitialized)) := by
  have source := NFQ_ZeroPrimitives.index_read bytes i inside value read
  unfold r1_pool_adapter.owned.require_zero_loop
  rw [Aeneas.Std.loop.eq_def]
  simp [r1_pool_adapter.owned.require_zero_loop.body,
    if_pos (show i < Slice.len bytes from inside),source,nonzero]

/-- Reject after precisely n zero bytes; later bytes are unrestricted. -/
theorem reject_after (bytes : Slice U8) (bound : bytes.val.length ≤ 4096)
    (n : Nat) (i : Usize) (value : U8)
    (inside : i.val + n < bytes.val.length)
    (zeroPrefix : ∀ j < n, bytes.val[i.val+j]? = some 0#u8)
    (read : bytes.val[i.val+n]? = some value) (nonzero : value ≠ 0#u8) :
    r1_pool_adapter.owned.require_zero_loop bytes i =
      ok (some (.Err solana_program_error.ProgramError.AccountAlreadyInitialized)) := by
  induction n generalizing i with
  | zero => exact reject_at bytes i value (by omega) (by simpa using read) nonzero
  | succ n ih =>
    have hi : i.val < bytes.val.length := by omega
    have first : Slice.index_usize bytes i = ok 0#u8 :=
      NFQ_ZeroPrimitives.index_read bytes i hi 0#u8 (by simpa using zeroPrefix 0 (by omega))
    have inc : (Usize.wrapping_add i 1#usize).val = i.val+1 :=
      NFQ_ZeroPrimitives.wrap_add i 1#usize (by change i.val+1≤4096;omega)
    have rest := ih (Usize.wrapping_add i 1#usize) (by rw [inc];omega)
      (by intro j hj;rw [inc];simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using zeroPrefix (j+1) (by omega))
      (by rw [inc];simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using read)
    unfold r1_pool_adapter.owned.require_zero_loop
    rw [Aeneas.Std.loop.eq_def]
    simp only [r1_pool_adapter.owned.require_zero_loop.body,
      if_pos (show i<Slice.len bytes from hi),first,
      show (0#u8 != 0#u8)=false from rfl,Bool.false_eq_true,if_false,lift,bind_tc_ok]
    simpa only [r1_pool_adapter.owned.require_zero_loop,
      r1_pool_adapter.owned.require_zero_loop.body,lift,bind_tc_ok] using rest

#print axioms reject_at
#print axioms reject_after
end NFQ_ZeroGateModel
