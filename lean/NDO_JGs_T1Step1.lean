import NDO_JGs_T1Data
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGs_T1
open Aeneas Aeneas.Std Result ControlFlow
theorem step4 : FIo_Native.weights.Weights.tensor_loop0_loop0.body JGq_PairShape.w 1#usize 4#usize 3#usize
    (FJa_ReverseStep.cursor 1#usize) s4=ok (.cont (FJa_ReverseStep.cursor 0#usize,s5)) := by
  obtain ⟨idx,hi,hn⟩ := FJa_ReverseStep.step 1#usize (by decide)
  have eq : idx=0#usize := UScalar.eq_of_val_eq (by change idx.val=0;change idx.val+1=1 at hi;omega)
  subst idx
  unfold FJa_ReverseStep.next at hn
  unfold FIo_Native.weights.Weights.tensor_loop0_loop0.body
  rw [hn,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  have mul0 : Usize.wrapping_mul 0#usize 4#usize=0#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 0#usize 4#usize (by decide))
  have add0 : Usize.wrapping_add 0#usize 0#usize=0#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 0#usize 0#usize (by decide))
  have mul1 : Usize.wrapping_mul 1#usize 4#usize=4#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 1#usize 4#usize (by decide))
  have add1 : Usize.wrapping_add 0#usize 4#usize=4#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 0#usize 4#usize (by decide))
  have mul2 : Usize.wrapping_mul 2#usize 4#usize=8#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 2#usize 4#usize (by decide))
  have add2 : Usize.wrapping_add 0#usize 8#usize=8#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 0#usize 8#usize (by decide))
  have mul3 : Usize.wrapping_mul 3#usize 4#usize=12#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 3#usize 4#usize (by decide))
  have add3 : Usize.wrapping_add 0#usize 12#usize=12#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 0#usize 12#usize (by decide))
  simp only [lift,bind_tc_ok,mul0,mul1,mul2,mul3,add0,add1,add2,add3]
  with_unfolding_all rfl
#print axioms step4
theorem step5 : FIo_Native.weights.Weights.tensor_loop0_loop0.body JGq_PairShape.w 1#usize 16#usize 4#usize
    (FJa_ReverseStep.cursor 16#usize) s5=ok (.cont (FJa_ReverseStep.cursor 15#usize,s6)) := by
  obtain ⟨idx,hi,hn⟩ := FJa_ReverseStep.step 16#usize (by decide)
  have eq : idx=15#usize := UScalar.eq_of_val_eq (by change idx.val=15;change idx.val+1=16 at hi;omega)
  subst idx
  unfold FJa_ReverseStep.next at hn
  unfold FIo_Native.weights.Weights.tensor_loop0_loop0.body
  rw [hn,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  have mul0 : Usize.wrapping_mul 0#usize 16#usize=0#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 0#usize 16#usize (by decide))
  have add0 : Usize.wrapping_add 15#usize 0#usize=15#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 15#usize 0#usize (by decide))
  have mul1 : Usize.wrapping_mul 1#usize 16#usize=16#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 1#usize 16#usize (by decide))
  have add1 : Usize.wrapping_add 15#usize 16#usize=31#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 15#usize 16#usize (by decide))
  have mul2 : Usize.wrapping_mul 2#usize 16#usize=32#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 2#usize 16#usize (by decide))
  have add2 : Usize.wrapping_add 15#usize 32#usize=47#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 15#usize 32#usize (by decide))
  have mul3 : Usize.wrapping_mul 3#usize 16#usize=48#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 3#usize 16#usize (by decide))
  have add3 : Usize.wrapping_add 15#usize 48#usize=63#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 15#usize 48#usize (by decide))
  simp only [lift,bind_tc_ok,mul0,mul1,mul2,mul3,add0,add1,add2,add3]
  with_unfolding_all rfl
#print axioms step5
theorem step6 : FIo_Native.weights.Weights.tensor_loop0_loop0.body JGq_PairShape.w 1#usize 16#usize 4#usize
    (FJa_ReverseStep.cursor 15#usize) s6=ok (.cont (FJa_ReverseStep.cursor 14#usize,s7)) := by
  obtain ⟨idx,hi,hn⟩ := FJa_ReverseStep.step 15#usize (by decide)
  have eq : idx=14#usize := UScalar.eq_of_val_eq (by change idx.val=14;change idx.val+1=15 at hi;omega)
  subst idx
  unfold FJa_ReverseStep.next at hn
  unfold FIo_Native.weights.Weights.tensor_loop0_loop0.body
  rw [hn,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  have mul0 : Usize.wrapping_mul 0#usize 16#usize=0#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 0#usize 16#usize (by decide))
  have add0 : Usize.wrapping_add 14#usize 0#usize=14#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 14#usize 0#usize (by decide))
  have mul1 : Usize.wrapping_mul 1#usize 16#usize=16#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 1#usize 16#usize (by decide))
  have add1 : Usize.wrapping_add 14#usize 16#usize=30#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 14#usize 16#usize (by decide))
  have mul2 : Usize.wrapping_mul 2#usize 16#usize=32#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 2#usize 16#usize (by decide))
  have add2 : Usize.wrapping_add 14#usize 32#usize=46#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 14#usize 32#usize (by decide))
  have mul3 : Usize.wrapping_mul 3#usize 16#usize=48#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 3#usize 16#usize (by decide))
  have add3 : Usize.wrapping_add 14#usize 48#usize=62#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 14#usize 48#usize (by decide))
  simp only [lift,bind_tc_ok,mul0,mul1,mul2,mul3,add0,add1,add2,add3]
  with_unfolding_all rfl
#print axioms step6
theorem step7 : FIo_Native.weights.Weights.tensor_loop0_loop0.body JGq_PairShape.w 1#usize 16#usize 4#usize
    (FJa_ReverseStep.cursor 14#usize) s7=ok (.cont (FJa_ReverseStep.cursor 13#usize,s8)) := by
  obtain ⟨idx,hi,hn⟩ := FJa_ReverseStep.step 14#usize (by decide)
  have eq : idx=13#usize := UScalar.eq_of_val_eq (by change idx.val=13;change idx.val+1=14 at hi;omega)
  subst idx
  unfold FJa_ReverseStep.next at hn
  unfold FIo_Native.weights.Weights.tensor_loop0_loop0.body
  rw [hn,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  have mul0 : Usize.wrapping_mul 0#usize 16#usize=0#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 0#usize 16#usize (by decide))
  have add0 : Usize.wrapping_add 13#usize 0#usize=13#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 13#usize 0#usize (by decide))
  have mul1 : Usize.wrapping_mul 1#usize 16#usize=16#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 1#usize 16#usize (by decide))
  have add1 : Usize.wrapping_add 13#usize 16#usize=29#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 13#usize 16#usize (by decide))
  have mul2 : Usize.wrapping_mul 2#usize 16#usize=32#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 2#usize 16#usize (by decide))
  have add2 : Usize.wrapping_add 13#usize 32#usize=45#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 13#usize 32#usize (by decide))
  have mul3 : Usize.wrapping_mul 3#usize 16#usize=48#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 3#usize 16#usize (by decide))
  have add3 : Usize.wrapping_add 13#usize 48#usize=61#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 13#usize 48#usize (by decide))
  simp only [lift,bind_tc_ok,mul0,mul1,mul2,mul3,add0,add1,add2,add3]
  with_unfolding_all rfl
#print axioms step7
end AspisR1.JGs_T1
end
