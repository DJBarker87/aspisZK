import NDO_JGs_T1Data
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGs_T1
open Aeneas Aeneas.Std Result ControlFlow
theorem step0 : FIo_Native.weights.Weights.tensor_loop0_loop0.body JGq_PairShape.w 1#usize 1#usize 2#usize
    (FJa_ReverseStep.cursor 1#usize) s0=ok (.cont (FJa_ReverseStep.cursor 0#usize,s1)) := by
  obtain ⟨idx,hi,hn⟩ := FJa_ReverseStep.step 1#usize (by decide)
  have eq : idx=0#usize := UScalar.eq_of_val_eq (by change idx.val=0;change idx.val+1=1 at hi;omega)
  subst idx
  unfold FJa_ReverseStep.next at hn
  unfold FIo_Native.weights.Weights.tensor_loop0_loop0.body
  rw [hn,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  have mul0 : Usize.wrapping_mul 0#usize 1#usize=0#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 0#usize 1#usize (by decide))
  have add0 : Usize.wrapping_add 0#usize 0#usize=0#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 0#usize 0#usize (by decide))
  have mul1 : Usize.wrapping_mul 1#usize 1#usize=1#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 1#usize 1#usize (by decide))
  have add1 : Usize.wrapping_add 0#usize 1#usize=1#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 0#usize 1#usize (by decide))
  have mul2 : Usize.wrapping_mul 2#usize 1#usize=2#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 2#usize 1#usize (by decide))
  have add2 : Usize.wrapping_add 0#usize 2#usize=2#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 0#usize 2#usize (by decide))
  have mul3 : Usize.wrapping_mul 3#usize 1#usize=3#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 3#usize 1#usize (by decide))
  have add3 : Usize.wrapping_add 0#usize 3#usize=3#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 0#usize 3#usize (by decide))
  simp only [lift,bind_tc_ok,mul0,mul1,mul2,mul3,add0,add1,add2,add3]
  with_unfolding_all rfl
#print axioms step0
theorem step1 : FIo_Native.weights.Weights.tensor_loop0_loop0.body JGq_PairShape.w 1#usize 4#usize 3#usize
    (FJa_ReverseStep.cursor 4#usize) s1=ok (.cont (FJa_ReverseStep.cursor 3#usize,s2)) := by
  obtain ⟨idx,hi,hn⟩ := FJa_ReverseStep.step 4#usize (by decide)
  have eq : idx=3#usize := UScalar.eq_of_val_eq (by change idx.val=3;change idx.val+1=4 at hi;omega)
  subst idx
  unfold FJa_ReverseStep.next at hn
  unfold FIo_Native.weights.Weights.tensor_loop0_loop0.body
  rw [hn,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  have mul0 : Usize.wrapping_mul 0#usize 4#usize=0#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 0#usize 4#usize (by decide))
  have add0 : Usize.wrapping_add 3#usize 0#usize=3#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 3#usize 0#usize (by decide))
  have mul1 : Usize.wrapping_mul 1#usize 4#usize=4#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 1#usize 4#usize (by decide))
  have add1 : Usize.wrapping_add 3#usize 4#usize=7#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 3#usize 4#usize (by decide))
  have mul2 : Usize.wrapping_mul 2#usize 4#usize=8#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 2#usize 4#usize (by decide))
  have add2 : Usize.wrapping_add 3#usize 8#usize=11#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 3#usize 8#usize (by decide))
  have mul3 : Usize.wrapping_mul 3#usize 4#usize=12#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 3#usize 4#usize (by decide))
  have add3 : Usize.wrapping_add 3#usize 12#usize=15#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 3#usize 12#usize (by decide))
  simp only [lift,bind_tc_ok,mul0,mul1,mul2,mul3,add0,add1,add2,add3]
  with_unfolding_all rfl
#print axioms step1
theorem step2 : FIo_Native.weights.Weights.tensor_loop0_loop0.body JGq_PairShape.w 1#usize 4#usize 3#usize
    (FJa_ReverseStep.cursor 3#usize) s2=ok (.cont (FJa_ReverseStep.cursor 2#usize,s3)) := by
  obtain ⟨idx,hi,hn⟩ := FJa_ReverseStep.step 3#usize (by decide)
  have eq : idx=2#usize := UScalar.eq_of_val_eq (by change idx.val=2;change idx.val+1=3 at hi;omega)
  subst idx
  unfold FJa_ReverseStep.next at hn
  unfold FIo_Native.weights.Weights.tensor_loop0_loop0.body
  rw [hn,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  have mul0 : Usize.wrapping_mul 0#usize 4#usize=0#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 0#usize 4#usize (by decide))
  have add0 : Usize.wrapping_add 2#usize 0#usize=2#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 2#usize 0#usize (by decide))
  have mul1 : Usize.wrapping_mul 1#usize 4#usize=4#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 1#usize 4#usize (by decide))
  have add1 : Usize.wrapping_add 2#usize 4#usize=6#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 2#usize 4#usize (by decide))
  have mul2 : Usize.wrapping_mul 2#usize 4#usize=8#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 2#usize 4#usize (by decide))
  have add2 : Usize.wrapping_add 2#usize 8#usize=10#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 2#usize 8#usize (by decide))
  have mul3 : Usize.wrapping_mul 3#usize 4#usize=12#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 3#usize 4#usize (by decide))
  have add3 : Usize.wrapping_add 2#usize 12#usize=14#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 2#usize 12#usize (by decide))
  simp only [lift,bind_tc_ok,mul0,mul1,mul2,mul3,add0,add1,add2,add3]
  with_unfolding_all rfl
#print axioms step2
theorem step3 : FIo_Native.weights.Weights.tensor_loop0_loop0.body JGq_PairShape.w 1#usize 4#usize 3#usize
    (FJa_ReverseStep.cursor 2#usize) s3=ok (.cont (FJa_ReverseStep.cursor 1#usize,s4)) := by
  obtain ⟨idx,hi,hn⟩ := FJa_ReverseStep.step 2#usize (by decide)
  have eq : idx=1#usize := UScalar.eq_of_val_eq (by change idx.val=1;change idx.val+1=2 at hi;omega)
  subst idx
  unfold FJa_ReverseStep.next at hn
  unfold FIo_Native.weights.Weights.tensor_loop0_loop0.body
  rw [hn,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  have mul0 : Usize.wrapping_mul 0#usize 4#usize=0#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 0#usize 4#usize (by decide))
  have add0 : Usize.wrapping_add 1#usize 0#usize=1#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 1#usize 0#usize (by decide))
  have mul1 : Usize.wrapping_mul 1#usize 4#usize=4#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 1#usize 4#usize (by decide))
  have add1 : Usize.wrapping_add 1#usize 4#usize=5#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 1#usize 4#usize (by decide))
  have mul2 : Usize.wrapping_mul 2#usize 4#usize=8#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 2#usize 4#usize (by decide))
  have add2 : Usize.wrapping_add 1#usize 8#usize=9#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 1#usize 8#usize (by decide))
  have mul3 : Usize.wrapping_mul 3#usize 4#usize=12#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 3#usize 4#usize (by decide))
  have add3 : Usize.wrapping_add 1#usize 12#usize=13#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 1#usize 12#usize (by decide))
  simp only [lift,bind_tc_ok,mul0,mul1,mul2,mul3,add0,add1,add2,add3]
  with_unfolding_all rfl
#print axioms step3
end AspisR1.JGs_T1
end
