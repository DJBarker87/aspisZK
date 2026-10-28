import NDO_JGs_T3Data
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGs_T3
open Aeneas Aeneas.Std Result ControlFlow
theorem step8 : FIo_Native.weights.Weights.tensor_loop0_loop0.body JGq_PairShape.w 3#usize 16#usize 4#usize
    (FJa_ReverseStep.cursor 13#usize) s8=ok (.cont (FJa_ReverseStep.cursor 12#usize,s9)) := by
  obtain ⟨idx,hi,hn⟩ := FJa_ReverseStep.step 13#usize (by decide)
  have eq : idx=12#usize := UScalar.eq_of_val_eq (by change idx.val=12;change idx.val+1=13 at hi;omega)
  subst idx
  unfold FJa_ReverseStep.next at hn
  unfold FIo_Native.weights.Weights.tensor_loop0_loop0.body
  rw [hn,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  have mul0 : Usize.wrapping_mul 0#usize 16#usize=0#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 0#usize 16#usize (by decide))
  have add0 : Usize.wrapping_add 12#usize 0#usize=12#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 12#usize 0#usize (by decide))
  have mul1 : Usize.wrapping_mul 1#usize 16#usize=16#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 1#usize 16#usize (by decide))
  have add1 : Usize.wrapping_add 12#usize 16#usize=28#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 12#usize 16#usize (by decide))
  have mul2 : Usize.wrapping_mul 2#usize 16#usize=32#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 2#usize 16#usize (by decide))
  have add2 : Usize.wrapping_add 12#usize 32#usize=44#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 12#usize 32#usize (by decide))
  have mul3 : Usize.wrapping_mul 3#usize 16#usize=48#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 3#usize 16#usize (by decide))
  have add3 : Usize.wrapping_add 12#usize 48#usize=60#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 12#usize 48#usize (by decide))
  simp only [lift,bind_tc_ok,mul0,mul1,mul2,mul3,add0,add1,add2,add3]
  with_unfolding_all rfl
#print axioms step8
theorem step9 : FIo_Native.weights.Weights.tensor_loop0_loop0.body JGq_PairShape.w 3#usize 16#usize 4#usize
    (FJa_ReverseStep.cursor 12#usize) s9=ok (.cont (FJa_ReverseStep.cursor 11#usize,s10)) := by
  obtain ⟨idx,hi,hn⟩ := FJa_ReverseStep.step 12#usize (by decide)
  have eq : idx=11#usize := UScalar.eq_of_val_eq (by change idx.val=11;change idx.val+1=12 at hi;omega)
  subst idx
  unfold FJa_ReverseStep.next at hn
  unfold FIo_Native.weights.Weights.tensor_loop0_loop0.body
  rw [hn,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  have mul0 : Usize.wrapping_mul 0#usize 16#usize=0#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 0#usize 16#usize (by decide))
  have add0 : Usize.wrapping_add 11#usize 0#usize=11#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 11#usize 0#usize (by decide))
  have mul1 : Usize.wrapping_mul 1#usize 16#usize=16#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 1#usize 16#usize (by decide))
  have add1 : Usize.wrapping_add 11#usize 16#usize=27#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 11#usize 16#usize (by decide))
  have mul2 : Usize.wrapping_mul 2#usize 16#usize=32#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 2#usize 16#usize (by decide))
  have add2 : Usize.wrapping_add 11#usize 32#usize=43#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 11#usize 32#usize (by decide))
  have mul3 : Usize.wrapping_mul 3#usize 16#usize=48#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 3#usize 16#usize (by decide))
  have add3 : Usize.wrapping_add 11#usize 48#usize=59#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 11#usize 48#usize (by decide))
  simp only [lift,bind_tc_ok,mul0,mul1,mul2,mul3,add0,add1,add2,add3]
  with_unfolding_all rfl
#print axioms step9
theorem step10 : FIo_Native.weights.Weights.tensor_loop0_loop0.body JGq_PairShape.w 3#usize 16#usize 4#usize
    (FJa_ReverseStep.cursor 11#usize) s10=ok (.cont (FJa_ReverseStep.cursor 10#usize,s11)) := by
  obtain ⟨idx,hi,hn⟩ := FJa_ReverseStep.step 11#usize (by decide)
  have eq : idx=10#usize := UScalar.eq_of_val_eq (by change idx.val=10;change idx.val+1=11 at hi;omega)
  subst idx
  unfold FJa_ReverseStep.next at hn
  unfold FIo_Native.weights.Weights.tensor_loop0_loop0.body
  rw [hn,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  have mul0 : Usize.wrapping_mul 0#usize 16#usize=0#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 0#usize 16#usize (by decide))
  have add0 : Usize.wrapping_add 10#usize 0#usize=10#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 10#usize 0#usize (by decide))
  have mul1 : Usize.wrapping_mul 1#usize 16#usize=16#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 1#usize 16#usize (by decide))
  have add1 : Usize.wrapping_add 10#usize 16#usize=26#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 10#usize 16#usize (by decide))
  have mul2 : Usize.wrapping_mul 2#usize 16#usize=32#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 2#usize 16#usize (by decide))
  have add2 : Usize.wrapping_add 10#usize 32#usize=42#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 10#usize 32#usize (by decide))
  have mul3 : Usize.wrapping_mul 3#usize 16#usize=48#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 3#usize 16#usize (by decide))
  have add3 : Usize.wrapping_add 10#usize 48#usize=58#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 10#usize 48#usize (by decide))
  simp only [lift,bind_tc_ok,mul0,mul1,mul2,mul3,add0,add1,add2,add3]
  with_unfolding_all rfl
#print axioms step10
theorem step11 : FIo_Native.weights.Weights.tensor_loop0_loop0.body JGq_PairShape.w 3#usize 16#usize 4#usize
    (FJa_ReverseStep.cursor 10#usize) s11=ok (.cont (FJa_ReverseStep.cursor 9#usize,s12)) := by
  obtain ⟨idx,hi,hn⟩ := FJa_ReverseStep.step 10#usize (by decide)
  have eq : idx=9#usize := UScalar.eq_of_val_eq (by change idx.val=9;change idx.val+1=10 at hi;omega)
  subst idx
  unfold FJa_ReverseStep.next at hn
  unfold FIo_Native.weights.Weights.tensor_loop0_loop0.body
  rw [hn,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  have mul0 : Usize.wrapping_mul 0#usize 16#usize=0#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 0#usize 16#usize (by decide))
  have add0 : Usize.wrapping_add 9#usize 0#usize=9#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 9#usize 0#usize (by decide))
  have mul1 : Usize.wrapping_mul 1#usize 16#usize=16#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 1#usize 16#usize (by decide))
  have add1 : Usize.wrapping_add 9#usize 16#usize=25#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 9#usize 16#usize (by decide))
  have mul2 : Usize.wrapping_mul 2#usize 16#usize=32#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 2#usize 16#usize (by decide))
  have add2 : Usize.wrapping_add 9#usize 32#usize=41#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 9#usize 32#usize (by decide))
  have mul3 : Usize.wrapping_mul 3#usize 16#usize=48#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 3#usize 16#usize (by decide))
  have add3 : Usize.wrapping_add 9#usize 48#usize=57#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 9#usize 48#usize (by decide))
  simp only [lift,bind_tc_ok,mul0,mul1,mul2,mul3,add0,add1,add2,add3]
  with_unfolding_all rfl
#print axioms step11
theorem step12 : FIo_Native.weights.Weights.tensor_loop0_loop0.body JGq_PairShape.w 3#usize 16#usize 4#usize
    (FJa_ReverseStep.cursor 9#usize) s12=ok (.cont (FJa_ReverseStep.cursor 8#usize,s13)) := by
  obtain ⟨idx,hi,hn⟩ := FJa_ReverseStep.step 9#usize (by decide)
  have eq : idx=8#usize := UScalar.eq_of_val_eq (by change idx.val=8;change idx.val+1=9 at hi;omega)
  subst idx
  unfold FJa_ReverseStep.next at hn
  unfold FIo_Native.weights.Weights.tensor_loop0_loop0.body
  rw [hn,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  have mul0 : Usize.wrapping_mul 0#usize 16#usize=0#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 0#usize 16#usize (by decide))
  have add0 : Usize.wrapping_add 8#usize 0#usize=8#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 8#usize 0#usize (by decide))
  have mul1 : Usize.wrapping_mul 1#usize 16#usize=16#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 1#usize 16#usize (by decide))
  have add1 : Usize.wrapping_add 8#usize 16#usize=24#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 8#usize 16#usize (by decide))
  have mul2 : Usize.wrapping_mul 2#usize 16#usize=32#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 2#usize 16#usize (by decide))
  have add2 : Usize.wrapping_add 8#usize 32#usize=40#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 8#usize 32#usize (by decide))
  have mul3 : Usize.wrapping_mul 3#usize 16#usize=48#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 3#usize 16#usize (by decide))
  have add3 : Usize.wrapping_add 8#usize 48#usize=56#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 8#usize 48#usize (by decide))
  simp only [lift,bind_tc_ok,mul0,mul1,mul2,mul3,add0,add1,add2,add3]
  with_unfolding_all rfl
#print axioms step12
theorem step13 : FIo_Native.weights.Weights.tensor_loop0_loop0.body JGq_PairShape.w 3#usize 16#usize 4#usize
    (FJa_ReverseStep.cursor 8#usize) s13=ok (.cont (FJa_ReverseStep.cursor 7#usize,s14)) := by
  obtain ⟨idx,hi,hn⟩ := FJa_ReverseStep.step 8#usize (by decide)
  have eq : idx=7#usize := UScalar.eq_of_val_eq (by change idx.val=7;change idx.val+1=8 at hi;omega)
  subst idx
  unfold FJa_ReverseStep.next at hn
  unfold FIo_Native.weights.Weights.tensor_loop0_loop0.body
  rw [hn,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  have mul0 : Usize.wrapping_mul 0#usize 16#usize=0#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 0#usize 16#usize (by decide))
  have add0 : Usize.wrapping_add 7#usize 0#usize=7#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 7#usize 0#usize (by decide))
  have mul1 : Usize.wrapping_mul 1#usize 16#usize=16#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 1#usize 16#usize (by decide))
  have add1 : Usize.wrapping_add 7#usize 16#usize=23#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 7#usize 16#usize (by decide))
  have mul2 : Usize.wrapping_mul 2#usize 16#usize=32#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 2#usize 16#usize (by decide))
  have add2 : Usize.wrapping_add 7#usize 32#usize=39#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 7#usize 32#usize (by decide))
  have mul3 : Usize.wrapping_mul 3#usize 16#usize=48#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 3#usize 16#usize (by decide))
  have add3 : Usize.wrapping_add 7#usize 48#usize=55#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 7#usize 48#usize (by decide))
  simp only [lift,bind_tc_ok,mul0,mul1,mul2,mul3,add0,add1,add2,add3]
  with_unfolding_all rfl
#print axioms step13
theorem step14 : FIo_Native.weights.Weights.tensor_loop0_loop0.body JGq_PairShape.w 3#usize 16#usize 4#usize
    (FJa_ReverseStep.cursor 7#usize) s14=ok (.cont (FJa_ReverseStep.cursor 6#usize,s15)) := by
  obtain ⟨idx,hi,hn⟩ := FJa_ReverseStep.step 7#usize (by decide)
  have eq : idx=6#usize := UScalar.eq_of_val_eq (by change idx.val=6;change idx.val+1=7 at hi;omega)
  subst idx
  unfold FJa_ReverseStep.next at hn
  unfold FIo_Native.weights.Weights.tensor_loop0_loop0.body
  rw [hn,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  have mul0 : Usize.wrapping_mul 0#usize 16#usize=0#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 0#usize 16#usize (by decide))
  have add0 : Usize.wrapping_add 6#usize 0#usize=6#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 6#usize 0#usize (by decide))
  have mul1 : Usize.wrapping_mul 1#usize 16#usize=16#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 1#usize 16#usize (by decide))
  have add1 : Usize.wrapping_add 6#usize 16#usize=22#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 6#usize 16#usize (by decide))
  have mul2 : Usize.wrapping_mul 2#usize 16#usize=32#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 2#usize 16#usize (by decide))
  have add2 : Usize.wrapping_add 6#usize 32#usize=38#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 6#usize 32#usize (by decide))
  have mul3 : Usize.wrapping_mul 3#usize 16#usize=48#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 3#usize 16#usize (by decide))
  have add3 : Usize.wrapping_add 6#usize 48#usize=54#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 6#usize 48#usize (by decide))
  simp only [lift,bind_tc_ok,mul0,mul1,mul2,mul3,add0,add1,add2,add3]
  with_unfolding_all rfl
#print axioms step14
theorem step15 : FIo_Native.weights.Weights.tensor_loop0_loop0.body JGq_PairShape.w 3#usize 16#usize 4#usize
    (FJa_ReverseStep.cursor 6#usize) s15=ok (.cont (FJa_ReverseStep.cursor 5#usize,s16)) := by
  obtain ⟨idx,hi,hn⟩ := FJa_ReverseStep.step 6#usize (by decide)
  have eq : idx=5#usize := UScalar.eq_of_val_eq (by change idx.val=5;change idx.val+1=6 at hi;omega)
  subst idx
  unfold FJa_ReverseStep.next at hn
  unfold FIo_Native.weights.Weights.tensor_loop0_loop0.body
  rw [hn,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  have mul0 : Usize.wrapping_mul 0#usize 16#usize=0#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 0#usize 16#usize (by decide))
  have add0 : Usize.wrapping_add 5#usize 0#usize=5#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 5#usize 0#usize (by decide))
  have mul1 : Usize.wrapping_mul 1#usize 16#usize=16#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 1#usize 16#usize (by decide))
  have add1 : Usize.wrapping_add 5#usize 16#usize=21#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 5#usize 16#usize (by decide))
  have mul2 : Usize.wrapping_mul 2#usize 16#usize=32#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 2#usize 16#usize (by decide))
  have add2 : Usize.wrapping_add 5#usize 32#usize=37#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 5#usize 32#usize (by decide))
  have mul3 : Usize.wrapping_mul 3#usize 16#usize=48#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 3#usize 16#usize (by decide))
  have add3 : Usize.wrapping_add 5#usize 48#usize=53#usize := UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 5#usize 48#usize (by decide))
  simp only [lift,bind_tc_ok,mul0,mul1,mul2,mul3,add0,add1,add2,add3]
  with_unfolding_all rfl
#print axioms step15
end AspisR1.JGs_T3
end
