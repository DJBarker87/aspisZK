import NIJ_CheckpointAdvance
import NGJ_VERIFIER_IMPORT
set_option autoImplicit false
namespace NIJ_CheckpointZeroStep
open Aeneas Aeneas.Std Result
abbrev body := AdapterRw.r1_pool_adapter.owned.require_zero_loop.body

theorem terminal (b : Slice U8) (i : Usize) (bound : b.val.length ≤ i.val) :
 body b i=ok (.done none) := by
 have h : ¬i<Slice.len b := by scalar_tac
 simp only [body,AdapterRw.r1_pool_adapter.owned.require_zero_loop.body,h,ite_false]

theorem step (b : Slice U8) (i : Usize) (cap : b.val.length ≤ 1768)
 (inside : i.val < b.val.length) :
 body b i = if NHY_ZeroStep.byte b i.val ≠ 0#u8 then
 ok (.done (some (.Err .AccountAlreadyInitialized)))
 else ok (.cont (i.wrapping_add 1#usize)) := by
 have h : i<Slice.len b := by scalar_tac
 simp only [body,AdapterRw.r1_pool_adapter.owned.require_zero_loop.body,h,ite_true,
  NHY_ZeroStep.read b i inside,bind_tc_ok]
 split <;> simp_all [lift]

/-- Native suffix packet's pre-state is the same selected original buffer. -/
theorem suffix_byte (b : Slice U8) (i k : Nat) (inside : i+k < b.val.length) :
 ((b.val.drop i)[k]?)=b.val[i+k]? := by
 simp only [List.getElem?_drop]

theorem next_value (b : Slice U8) (i : Usize) (cap : b.val.length ≤ 1768)
 (inside : i.val < b.val.length) : (i.wrapping_add 1#usize).val=i.val+1 :=
 NIJ_CheckpointAdvance.value i (by omega)

#print axioms terminal
#print axioms step
#print axioms suffix_byte
#print axioms next_value
end NIJ_CheckpointZeroStep

#print Aeneas.Std.lift
