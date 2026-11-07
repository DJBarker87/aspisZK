import NMT_345ZeroInduction
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result ControlFlow
open _root_.AdapterRw
/-- Complete symbolic scan, all bytes and both returned Results. The
induction variable is remaining length, never a concrete 1768-byte term. -/
theorem zero_all_loop (bytes : Slice U8) (n : Nat) (i : Usize)
 (left : i.val + n = bytes.val.length) :
 r1_pool_adapter.owned.require_zero_loop bytes i =
 .ok (if (bytes.val.drop i.val).all (· == 0#u8) then none
      else some (.Err solana_program_error.ProgramError.AccountAlreadyInitialized)) := by
 induction n generalizing i with
 | zero =>
   have eq : i.val = bytes.val.length := by omega
   have outside : ¬ i < Slice.len bytes := by change ¬ i.val < bytes.val.length; omega
   unfold r1_pool_adapter.owned.require_zero_loop
   rw [Aeneas.Std.loop.eq_def]
   simp only [r1_pool_adapter.owned.require_zero_loop.body, if_neg outside,
    eq, List.drop_length, List.all_nil, if_true]
 | succ n ih =>
   have inside : i.val < bytes.val.length := by omega
   let b : U8 := bytes.val[i.val]'inside
   have selected : bytes.val[i.val]? = some b := by
    simp only [b,List.getElem?_eq_getElem inside]
   have call := NFQ_ZeroPrimitives.index_read bytes i inside b selected
   have inc := zero_increment bytes i inside
   have tail := List.drop_eq_getElem_cons inside
   by_cases hz : b = 0#u8
   · have rest := ih (Usize.wrapping_add i 1#usize) (by rw [inc]; omega)
     unfold r1_pool_adapter.owned.require_zero_loop
     rw [Aeneas.Std.loop.eq_def]
     simp only [r1_pool_adapter.owned.require_zero_loop.body,
      if_pos (show i < Slice.len bytes from inside),call,hz,
      show (0#u8 != 0#u8) = false from rfl,Bool.false_eq_true,if_false,lift,bind_tc_ok]
     rw [tail]
     change _ = Result.ok (if ((b == 0#u8) && (bytes.val.drop (i.val+1)).all (· == 0#u8)) then (none : Option (core.result.Result Unit AdapterRw.solana_program_error.ProgramError)) else some (.Err AdapterRw.solana_program_error.ProgramError.AccountAlreadyInitialized))
     simp only [hz,beq_self_eq_true,Bool.true_and]
     simpa only [r1_pool_adapter.owned.require_zero_loop,
      r1_pool_adapter.owned.require_zero_loop.body,lift,bind_tc_ok,inc] using rest
   · rw [NFQ_ZeroGateModel.reject_at bytes i b inside selected hz]
     rw [tail]
     change _ = Result.ok (if ((b == 0#u8) && (bytes.val.drop (i.val+1)).all (· == 0#u8)) then (none : Option (core.result.Result Unit AdapterRw.solana_program_error.ProgramError)) else some (.Err AdapterRw.solana_program_error.ProgramError.AccountAlreadyInitialized))
     simp [hz]
#print axioms zero_all_loop
end NMT_345
