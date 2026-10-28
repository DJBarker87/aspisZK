import NDO_JGq_Powers1Data
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Powers1
open Aeneas Aeneas.Std Result ControlFlow
theorem step3 : FIo_Native.weights.powers_loop.body x a3 p3 3#usize=ok (.done a4) := by
  have inc : Usize.wrapping_add 3#usize 1#usize=4#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 3#usize 1#usize (by decide))
  unfold FIo_Native.weights.powers_loop.body
  rw [if_pos (by decide : 3#usize<4#usize)]
  have idx : Array.index_usize a3 3#usize=ok FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO := by rfl
  rw [Array.index_mut_usize,idx,bind_tc_ok]
  simp only [lift,bind_tc_ok,inc,Aeneas.Std.uncurry]
  rw [if_pos True.intro]
  rfl
#print axioms step3
end AspisR1.JGq_Powers1
end
