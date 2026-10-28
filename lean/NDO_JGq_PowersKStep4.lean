import NDO_JGq_PowersKData
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_PowersK
open Aeneas Aeneas.Std Result ControlFlow
theorem multiply4 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul p4 x=ok p5 := by with_unfolding_all rfl
#print axioms multiply4
theorem step4 : FIo_Native.weights.powers_loop.body x a4 p4 4#usize=ok (.cont (a5,p5,5#usize)) := by
  have inc : Usize.wrapping_add 4#usize 1#usize=5#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 4#usize 1#usize (by decide))
  unfold FIo_Native.weights.powers_loop.body
  rw [if_pos (by decide : 4#usize<7#usize)]
  have idx : Array.index_usize a4 4#usize=ok FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO := by rfl
  rw [Array.index_mut_usize,idx,bind_tc_ok]
  simp only [lift,bind_tc_ok,inc,Aeneas.Std.uncurry]
  rw [if_neg (by scalar_tac : 5#usize≠7#usize)]
  rw [multiply4,bind_tc_ok]
  rfl
#print axioms step4
end AspisR1.JGq_PowersK
end
