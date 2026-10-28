import R1Z.ProverRwFullFuns
import R1Z.ProverRw19LoopBind
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CompactHigh39
open Aeneas Aeneas.Std Result ProverRwFull

/-- Check exactly the high half of one logical wide encoding. The input
condition concerns individual bytes, not success of the source loop. -/
theorem complete (logical : Slice U8) (at1 : Usize) (n : Nat) (high : Usize)
    (bound : high.val+n=32) (lower : 16≤high.val)
    (zero : ∀ j : Usize, 16≤j.val → j.val<32 →
      Slice.index_usize logical (Usize.wrapping_add at1 j)=.ok 0#u8) :
    host_compact.compact_values_loop0_loop0 logical at1 high = .ok none := by
  induction n generalizing high with
  | zero =>
    unfold host_compact.compact_values_loop0_loop0
    rw [ProverRw19LoopBind.loop_bind]
    simp only [host_compact.compact_values_loop0_loop0.body,
      show ¬high<32#usize from (by change ¬high.val<32;omega),↓reduceIte,bind_tc_ok]
  | succ n ih =>
    have hh : high.val<32 := by omega
    have inc : (Usize.wrapping_add high 1#usize).val=high.val+1 := by
      rw [Usize.wrapping_add_val_eq]
      apply Nat.mod_eq_of_lt
      change high.val+1<UScalar.size .Usize
      have big := (32#usize).hSize
      change 32<UScalar.size .Usize at big
      omega
    have next := ih (Usize.wrapping_add high 1#usize) (by rw [inc];omega) (by rw [inc];omega)
    unfold host_compact.compact_values_loop0_loop0
    rw [ProverRw19LoopBind.loop_bind]
    simp only [host_compact.compact_values_loop0_loop0.body,
      show high<32#usize from hh,↓reduceIte,lift,bind_tc_ok,zero high lower hh]
    exact next

#print axioms complete
end R1Z.PV_RunJoin_CompactHigh39
