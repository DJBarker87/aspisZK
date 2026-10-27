import JGs_T1Data
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGs_T1
open Aeneas Aeneas.Std Result ControlFlow
theorem step0 : FIo_Native.weights.Weights.tensor_loop0_loop0.body JGq_PairShape.w 1#usize 1#usize 2#usize
    (FJa_ReverseStep.cursor 1#usize) s0=ok (.cont (FJa_ReverseStep.cursor 0#usize,s1)) := by
  with_unfolding_all rfl
#print axioms step0
theorem step1 : FIo_Native.weights.Weights.tensor_loop0_loop0.body JGq_PairShape.w 1#usize 4#usize 3#usize
    (FJa_ReverseStep.cursor 4#usize) s1=ok (.cont (FJa_ReverseStep.cursor 3#usize,s2)) := by
  with_unfolding_all rfl
#print axioms step1
theorem step2 : FIo_Native.weights.Weights.tensor_loop0_loop0.body JGq_PairShape.w 1#usize 4#usize 3#usize
    (FJa_ReverseStep.cursor 3#usize) s2=ok (.cont (FJa_ReverseStep.cursor 2#usize,s3)) := by
  with_unfolding_all rfl
#print axioms step2
theorem step3 : FIo_Native.weights.Weights.tensor_loop0_loop0.body JGq_PairShape.w 1#usize 4#usize 3#usize
    (FJa_ReverseStep.cursor 2#usize) s3=ok (.cont (FJa_ReverseStep.cursor 1#usize,s4)) := by
  with_unfolding_all rfl
#print axioms step3
end AspisR1.JGs_T1
end
