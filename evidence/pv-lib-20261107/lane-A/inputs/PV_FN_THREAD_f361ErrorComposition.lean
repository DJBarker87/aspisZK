import PV_FN_THREAD_f361ErrorChains
import PV_FN_THREAD_f361ErrorCall
import PV_FN_THREAD_f361ErrorMatch
import PV_FN_THREAD_f361ErrorDrops
import PV_FN_THREAD_f361ErrorReturn
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f361ErrorComposition
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
def programs : Data → Option PV_STX2_SliceSyntax.Program := fun _ => none
def steps {W E : Type} (B : Carrier W Data) (K : Control)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) : Nat :=
  let q0 := q
  let q1 := PV_FN_THREAD_f361ErrorChain0To4.after B q0
  let q2 := PV_FN_THREAD_f361ErrorCall280.after B H q1
  let q3 := PV_FN_THREAD_f361ErrorChain5To7.after B q2
  let q4 := PV_FN_THREAD_f361ErrorMatch7.after B K q3
  let q5 := PV_FN_THREAD_f361ErrorChain8To19.after B q4
  let q6 := PV_FN_THREAD_f361ErrorDrop19.after B H q5
  let q7 := PV_FN_THREAD_f361ErrorChain20To23.after B q6
  let q8 := PV_FN_THREAD_f361ErrorDrop23.after B H q7
  let q9 := PV_FN_THREAD_f361ErrorChain24To39.after B q8
  let q10 := PV_FN_THREAD_f361ErrorReturn.after B q9
  PV_FN_THREAD_f361ErrorChain0To4.steps B q0 + (PV_FN_THREAD_f361ErrorCall280.steps B q1 + (PV_FN_THREAD_f361ErrorChain5To7.steps B q2 + (PV_FN_THREAD_f361ErrorMatch7.steps B q3 + (PV_FN_THREAD_f361ErrorChain8To19.steps B q4 + (PV_FN_THREAD_f361ErrorDrop19.steps B q5 + (PV_FN_THREAD_f361ErrorChain20To23.steps B q6 + (PV_FN_THREAD_f361ErrorDrop23.steps B q7 + (PV_FN_THREAD_f361ErrorChain24To39.steps B q8 + (PV_FN_THREAD_f361ErrorReturn.steps B q9)))))))))
def after {W E : Type} (B : Carrier W Data) (K : Control)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) : PV_THR2_IntrinsicState.State W E :=
  let q0 := q
  let q1 := PV_FN_THREAD_f361ErrorChain0To4.after B q0
  let q2 := PV_FN_THREAD_f361ErrorCall280.after B H q1
  let q3 := PV_FN_THREAD_f361ErrorChain5To7.after B q2
  let q4 := PV_FN_THREAD_f361ErrorMatch7.after B K q3
  let q5 := PV_FN_THREAD_f361ErrorChain8To19.after B q4
  let q6 := PV_FN_THREAD_f361ErrorDrop19.after B H q5
  let q7 := PV_FN_THREAD_f361ErrorChain20To23.after B q6
  let q8 := PV_FN_THREAD_f361ErrorDrop23.after B H q7
  let q9 := PV_FN_THREAD_f361ErrorChain24To39.after B q8
  let q10 := PV_FN_THREAD_f361ErrorReturn.after B q9
  q10
/-- Source-only composition of the complete emitted error arm. Both Drop
requests, all full replies and early return administration are retained. No
caller continuation is traversed after this arm returns. Argument-effect and
own-entry joins remain separate contract obligations. -/
theorem run {W E : Type} (B : Carrier W Data) (K : Control)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance B K programs H (steps B K H q) q = after B K H q := by
  unfold steps after
  dsimp only
  rw [PV_THR2_IntrinsicComposition.advance_add]
  rw [PV_FN_THREAD_f361ErrorChain0To4.run B K programs H _]
  rw [PV_THR2_IntrinsicComposition.advance_add]
  rw [PV_FN_THREAD_f361ErrorCall280.run B K programs H _ (by rfl)]
  rw [PV_THR2_IntrinsicComposition.advance_add]
  rw [PV_FN_THREAD_f361ErrorChain5To7.run B K programs H _]
  rw [PV_THR2_IntrinsicComposition.advance_add]
  rw [PV_FN_THREAD_f361ErrorMatch7.run B K programs H _]
  rw [PV_THR2_IntrinsicComposition.advance_add]
  rw [PV_FN_THREAD_f361ErrorChain8To19.run B K programs H _]
  rw [PV_THR2_IntrinsicComposition.advance_add]
  rw [PV_FN_THREAD_f361ErrorDrop19.run B K programs H _]
  rw [PV_THR2_IntrinsicComposition.advance_add]
  rw [PV_FN_THREAD_f361ErrorChain20To23.run B K programs H _]
  rw [PV_THR2_IntrinsicComposition.advance_add]
  rw [PV_FN_THREAD_f361ErrorDrop23.run B K programs H _]
  rw [PV_THR2_IntrinsicComposition.advance_add]
  rw [PV_FN_THREAD_f361ErrorChain24To39.run B K programs H _]
  exact PV_FN_THREAD_f361ErrorReturn.run B K programs H _
#print axioms run
end PV_FN_THREAD_f361ErrorComposition
