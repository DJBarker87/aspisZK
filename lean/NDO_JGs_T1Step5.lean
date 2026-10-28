import NDO_JGs_T1Data
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGs_T1
open Aeneas Aeneas.Std Result ControlFlow
theorem step20 : FIo_Native.weights.Weights.tensor_loop0_loop0.body JGq_PairShape.w 1#usize 16#usize 4#usize
    (FJa_ReverseStep.cursor 1#usize) s20=ok (.cont (FJa_ReverseStep.cursor 0#usize,s21)) := by
  obtain ⟨idx,hi,hn⟩ := FJa_ReverseStep.step 1#usize (by decide)
  have eq : idx=0#usize := UScalar.eq_of_val_eq (by change idx.val=0;change idx.val+1=1 at hi;omega)
  subst idx
  unfold FJa_ReverseStep.next at hn
  unfold FIo_Native.weights.Weights.tensor_loop0_loop0.body
  rw [hn,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  have mul0 : Usize.wrapping_mul 0#usize 16#usize=0#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 0#usize 16#usize (by decide))
  have add0 : Usize.wrapping_add 0#usize 0#usize=0#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 0#usize 0#usize (by decide))
  have mul1 : Usize.wrapping_mul 1#usize 16#usize=16#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 1#usize 16#usize (by decide))
  have add1 : Usize.wrapping_add 0#usize 16#usize=16#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 0#usize 16#usize (by decide))
  have mul2 : Usize.wrapping_mul 2#usize 16#usize=32#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 2#usize 16#usize (by decide))
  have add2 : Usize.wrapping_add 0#usize 32#usize=32#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 0#usize 32#usize (by decide))
  have mul3 : Usize.wrapping_mul 3#usize 16#usize=48#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 3#usize 16#usize (by decide))
  have add3 : Usize.wrapping_add 0#usize 48#usize=48#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 0#usize 48#usize (by decide))
  simp only [lift,bind_tc_ok,mul0,mul1,mul2,mul3,add0,add1,add2,add3]
  with_unfolding_all rfl
#print axioms step20
end AspisR1.JGs_T1
end
