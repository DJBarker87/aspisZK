import NDO_JGq_PowersKData
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_PowersK
open Aeneas Aeneas.Std Result ControlFlow
theorem step6 : FIo_Native.weights.powers_loop.body x a6 p6 6#usize=ok (.done a7) := by
  have inc : Usize.wrapping_add 6#usize 1#usize=7#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 6#usize 1#usize (by decide))
  unfold FIo_Native.weights.powers_loop.body
  rw [if_pos (by decide : 6#usize<7#usize)]
  have idx : Array.index_usize a6 6#usize=ok FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO := by rfl
  rw [Array.index_mut_usize,idx,bind_tc_ok]
  simp only [lift,bind_tc_ok,inc,Aeneas.Std.uncurry]
  rw [if_pos True.intro]
  rfl
#print axioms step6
end AspisR1.JGq_PowersK
end
