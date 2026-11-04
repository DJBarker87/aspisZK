import NFB_TailProgram
set_option autoImplicit false
noncomputable section
namespace NFB_TailCuts
open Aeneas Aeneas.Std Result AspisR1 NFB_TailProgram

/-- All three receiver pre/post-states, inputs and return are cuts of ONE
actual tail computation. No independently selected child successes. -/
theorem complete (q : Array U8 608#usize) (g : Coeff) (slot : Usize) (out : E)
 (accepted : NFA_SuffixFactor.tail q g slot=ok out) :
 ∃ (s0 s1 s2 s3 : Dot) (e0 e1 e2 : E) (q0 q1 q2 : Q) (stride : Usize),
 FIo_Native.fast_pairing.EbyKDot.new=ok s0 ∧
 first q g slot=ok (e0,q0) ∧
 FIo_Native.fast_pairing.EbyKDot.push s0 e0 q0=ok (.Ok (),s1) ∧
 slot*32#usize=ok stride ∧ later q g stride 0#usize=ok (e1,q1) ∧
 FIo_Native.fast_pairing.EbyKDot.push s1 e1 q1=ok (.Ok (),s2) ∧
 later q g stride 1#usize=ok (e2,q2) ∧
 FIo_Native.fast_pairing.EbyKDot.push s2 e2 q2=ok (.Ok (),s3) ∧
 FIo_Native.fast_pairing.EbyKDot.finish s3=ok out := by
 rw [association] at accepted
 unfold run at accepted
 obtain ⟨s0,new,accepted⟩ := Port3_PushFrame.bind_success _ _ _ accepted
 obtain ⟨⟨e0,q0⟩,firstRun,accepted⟩ := Port3_PushFrame.bind_success _ _ _ accepted
 obtain ⟨s1,push0,accepted⟩ := Port3_PushFrame.bind_success _ _ _ accepted
 obtain ⟨stride,strideRun,accepted⟩ := Port3_PushFrame.bind_success _ _ _ accepted
 obtain ⟨⟨e1,q1⟩,secondRun,accepted⟩ := Port3_PushFrame.bind_success _ _ _ accepted
 obtain ⟨s2,push1,accepted⟩ := Port3_PushFrame.bind_success _ _ _ accepted
 obtain ⟨⟨e2,q2⟩,thirdRun,accepted⟩ := Port3_PushFrame.bind_success _ _ _ accepted
 obtain ⟨s3,push2,finish⟩ := Port3_PushFrame.bind_success _ _ _ accepted
 exact ⟨s0,s1,s2,s3,e0,e1,e2,q0,q1,q2,stride,new,firstRun,
  push_success _ _ _ _ push0,strideRun,secondRun,push_success _ _ _ _ push1,
  thirdRun,push_success _ _ _ _ push2,finish⟩
#print axioms complete
end NFB_TailCuts
end
