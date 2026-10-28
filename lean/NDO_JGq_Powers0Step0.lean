import NDO_JGq_Powers0Data
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Powers0
open Aeneas Aeneas.Std Result ControlFlow
theorem multiply0 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul p0 x=ok p1 := by with_unfolding_all rfl
#print axioms multiply0
theorem step0 : FIo_Native.weights.powers_loop.body x a0 p0 0#usize=ok (.cont (a1,p1,1#usize)) := by
  have inc : Usize.wrapping_add 0#usize 1#usize=1#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 0#usize 1#usize (by decide))
  unfold FIo_Native.weights.powers_loop.body
  rw [if_pos (by decide : 0#usize<4#usize)]
  have idx : Array.index_usize a0 0#usize=ok FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO := by rfl
  rw [Array.index_mut_usize,idx,bind_tc_ok]
  simp only [lift,bind_tc_ok,inc,Aeneas.Std.uncurry]
  rw [if_neg (by scalar_tac : 1#usize≠4#usize)]
  rw [multiply0,bind_tc_ok]
  rfl
#print axioms step0
end AspisR1.JGq_Powers0
end
