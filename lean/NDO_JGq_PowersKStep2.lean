import NDO_JGq_PowersKData
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_PowersK
open Aeneas Aeneas.Std Result ControlFlow
theorem multiply2 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul p2 x=ok p3 := by with_unfolding_all rfl
#print axioms multiply2
theorem step2 : FIo_Native.weights.powers_loop.body x a2 p2 2#usize=ok (.cont (a3,p3,3#usize)) := by
  have inc : Usize.wrapping_add 2#usize 1#usize=3#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 2#usize 1#usize (by decide))
  unfold FIo_Native.weights.powers_loop.body
  rw [if_pos (by decide : 2#usize<7#usize)]
  have idx : Array.index_usize a2 2#usize=ok FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO := by rfl
  rw [Array.index_mut_usize,idx,bind_tc_ok]
  simp only [lift,bind_tc_ok,inc,Aeneas.Std.uncurry]
  rw [if_neg (by scalar_tac : 3#usize≠7#usize)]
  rw [multiply2,bind_tc_ok]
  rfl
#print axioms step2
end AspisR1.JGq_PowersK
end
