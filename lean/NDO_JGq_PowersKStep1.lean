import NDO_JGq_PowersKData
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_PowersK
open Aeneas Aeneas.Std Result ControlFlow
theorem multiply1 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul p1 x=ok p2 := by with_unfolding_all rfl
#print axioms multiply1
theorem step1 : FIo_Native.weights.powers_loop.body x a1 p1 1#usize=ok (.cont (a2,p2,2#usize)) := by
  have inc : Usize.wrapping_add 1#usize 1#usize=2#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 1#usize 1#usize (by decide))
  unfold FIo_Native.weights.powers_loop.body
  rw [if_pos (by decide : 1#usize<7#usize)]
  have idx : Array.index_usize a1 1#usize=ok FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO := by rfl
  rw [Array.index_mut_usize,idx,bind_tc_ok]
  simp only [lift,bind_tc_ok,inc,Aeneas.Std.uncurry]
  rw [if_neg (by scalar_tac : 2#usize≠7#usize)]
  rw [multiply1,bind_tc_ok]
  rfl
#print axioms step1
end AspisR1.JGq_PowersK
end
