import NDO_JGs_T1Data
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGs_T1
open Aeneas Aeneas.Std Result ControlFlow
theorem step16 : FIo_Native.weights.Weights.tensor_loop0_loop0.body JGq_PairShape.w 1#usize 16#usize 4#usize
    (FJa_ReverseStep.cursor 5#usize) s16=ok (.cont (FJa_ReverseStep.cursor 4#usize,s17)) := by
  obtain ⟨idx,hi,hn⟩ := FJa_ReverseStep.step 5#usize (by decide)
  have eq : idx=4#usize := UScalar.eq_of_val_eq (by change idx.val=4;change idx.val+1=5 at hi;omega)
  subst idx
  unfold FJa_ReverseStep.next at hn
  unfold FIo_Native.weights.Weights.tensor_loop0_loop0.body
  rw [hn,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  have mul0 : Usize.wrapping_mul 0#usize 16#usize=0#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 0#usize 16#usize (by decide))
  have add0 : Usize.wrapping_add 4#usize 0#usize=4#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 4#usize 0#usize (by decide))
  have mul1 : Usize.wrapping_mul 1#usize 16#usize=16#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 1#usize 16#usize (by decide))
  have add1 : Usize.wrapping_add 4#usize 16#usize=20#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 4#usize 16#usize (by decide))
  have mul2 : Usize.wrapping_mul 2#usize 16#usize=32#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 2#usize 16#usize (by decide))
  have add2 : Usize.wrapping_add 4#usize 32#usize=36#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 4#usize 32#usize (by decide))
  have mul3 : Usize.wrapping_mul 3#usize 16#usize=48#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 3#usize 16#usize (by decide))
  have add3 : Usize.wrapping_add 4#usize 48#usize=52#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 4#usize 48#usize (by decide))
  simp only [lift,bind_tc_ok,mul0,mul1,mul2,mul3,add0,add1,add2,add3]
  with_unfolding_all rfl
#print axioms step16
theorem step17 : FIo_Native.weights.Weights.tensor_loop0_loop0.body JGq_PairShape.w 1#usize 16#usize 4#usize
    (FJa_ReverseStep.cursor 4#usize) s17=ok (.cont (FJa_ReverseStep.cursor 3#usize,s18)) := by
  obtain ⟨idx,hi,hn⟩ := FJa_ReverseStep.step 4#usize (by decide)
  have eq : idx=3#usize := UScalar.eq_of_val_eq (by change idx.val=3;change idx.val+1=4 at hi;omega)
  subst idx
  unfold FJa_ReverseStep.next at hn
  unfold FIo_Native.weights.Weights.tensor_loop0_loop0.body
  rw [hn,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  have mul0 : Usize.wrapping_mul 0#usize 16#usize=0#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 0#usize 16#usize (by decide))
  have add0 : Usize.wrapping_add 3#usize 0#usize=3#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 3#usize 0#usize (by decide))
  have mul1 : Usize.wrapping_mul 1#usize 16#usize=16#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 1#usize 16#usize (by decide))
  have add1 : Usize.wrapping_add 3#usize 16#usize=19#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 3#usize 16#usize (by decide))
  have mul2 : Usize.wrapping_mul 2#usize 16#usize=32#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 2#usize 16#usize (by decide))
  have add2 : Usize.wrapping_add 3#usize 32#usize=35#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 3#usize 32#usize (by decide))
  have mul3 : Usize.wrapping_mul 3#usize 16#usize=48#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 3#usize 16#usize (by decide))
  have add3 : Usize.wrapping_add 3#usize 48#usize=51#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 3#usize 48#usize (by decide))
  simp only [lift,bind_tc_ok,mul0,mul1,mul2,mul3,add0,add1,add2,add3]
  with_unfolding_all rfl
#print axioms step17
theorem step18 : FIo_Native.weights.Weights.tensor_loop0_loop0.body JGq_PairShape.w 1#usize 16#usize 4#usize
    (FJa_ReverseStep.cursor 3#usize) s18=ok (.cont (FJa_ReverseStep.cursor 2#usize,s19)) := by
  obtain ⟨idx,hi,hn⟩ := FJa_ReverseStep.step 3#usize (by decide)
  have eq : idx=2#usize := UScalar.eq_of_val_eq (by change idx.val=2;change idx.val+1=3 at hi;omega)
  subst idx
  unfold FJa_ReverseStep.next at hn
  unfold FIo_Native.weights.Weights.tensor_loop0_loop0.body
  rw [hn,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  have mul0 : Usize.wrapping_mul 0#usize 16#usize=0#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 0#usize 16#usize (by decide))
  have add0 : Usize.wrapping_add 2#usize 0#usize=2#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 2#usize 0#usize (by decide))
  have mul1 : Usize.wrapping_mul 1#usize 16#usize=16#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 1#usize 16#usize (by decide))
  have add1 : Usize.wrapping_add 2#usize 16#usize=18#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 2#usize 16#usize (by decide))
  have mul2 : Usize.wrapping_mul 2#usize 16#usize=32#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 2#usize 16#usize (by decide))
  have add2 : Usize.wrapping_add 2#usize 32#usize=34#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 2#usize 32#usize (by decide))
  have mul3 : Usize.wrapping_mul 3#usize 16#usize=48#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 3#usize 16#usize (by decide))
  have add3 : Usize.wrapping_add 2#usize 48#usize=50#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 2#usize 48#usize (by decide))
  simp only [lift,bind_tc_ok,mul0,mul1,mul2,mul3,add0,add1,add2,add3]
  with_unfolding_all rfl
#print axioms step18
theorem step19 : FIo_Native.weights.Weights.tensor_loop0_loop0.body JGq_PairShape.w 1#usize 16#usize 4#usize
    (FJa_ReverseStep.cursor 2#usize) s19=ok (.cont (FJa_ReverseStep.cursor 1#usize,s20)) := by
  obtain ⟨idx,hi,hn⟩ := FJa_ReverseStep.step 2#usize (by decide)
  have eq : idx=1#usize := UScalar.eq_of_val_eq (by change idx.val=1;change idx.val+1=2 at hi;omega)
  subst idx
  unfold FJa_ReverseStep.next at hn
  unfold FIo_Native.weights.Weights.tensor_loop0_loop0.body
  rw [hn,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  have mul0 : Usize.wrapping_mul 0#usize 16#usize=0#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 0#usize 16#usize (by decide))
  have add0 : Usize.wrapping_add 1#usize 0#usize=1#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 1#usize 0#usize (by decide))
  have mul1 : Usize.wrapping_mul 1#usize 16#usize=16#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 1#usize 16#usize (by decide))
  have add1 : Usize.wrapping_add 1#usize 16#usize=17#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 1#usize 16#usize (by decide))
  have mul2 : Usize.wrapping_mul 2#usize 16#usize=32#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 2#usize 16#usize (by decide))
  have add2 : Usize.wrapping_add 1#usize 32#usize=33#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 1#usize 32#usize (by decide))
  have mul3 : Usize.wrapping_mul 3#usize 16#usize=48#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 3#usize 16#usize (by decide))
  have add3 : Usize.wrapping_add 1#usize 48#usize=49#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 1#usize 48#usize (by decide))
  simp only [lift,bind_tc_ok,mul0,mul1,mul2,mul3,add0,add1,add2,add3]
  with_unfolding_all rfl
#print axioms step19
end AspisR1.JGs_T1
end
