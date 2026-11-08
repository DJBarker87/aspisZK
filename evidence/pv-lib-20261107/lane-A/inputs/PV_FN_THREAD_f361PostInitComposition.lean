import PV_FN_THREAD_f361PostInitChains
import PV_FN_THREAD_f361PostInitCalls
import PV_FN_THREAD_f361ReturnMatches
import PV_FN_THREAD_f361ReturnAggregates
import PV_FN_THREAD_f361Return
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f361PostInitHead
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
def programs : Data → Option PV_STX2_SliceSyntax.Program := fun _ => none
def steps {W E : Type} (B : Carrier W Data) (K : Control)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) : Nat :=
  let q0 := q
  let q1 := PV_FN_THREAD_f361Chain130To139.after B q0
  let q2 := PV_FN_THREAD_f361Call459PostInit.after B H q1
  let q3 := PV_FN_THREAD_f361Chain140To142.after B q2
  let q4 := PV_FN_THREAD_f361Call279PostInit.after B H q3
  let q5 := PV_FN_THREAD_f361Chain143To144.after B q4
  let q6 := PV_FN_THREAD_f361Match144.after B K q5
  PV_FN_THREAD_f361Chain130To139.steps B q0 + (PV_FN_THREAD_f361Call459PostInit.steps B q1 + (PV_FN_THREAD_f361Chain140To142.steps B q2 + (PV_FN_THREAD_f361Call279PostInit.steps B q3 + (PV_FN_THREAD_f361Chain143To144.steps B q4 + (PV_FN_THREAD_f361Match144.steps B q5)))))
def after {W E : Type} (B : Carrier W Data) (K : Control)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) : PV_THR2_IntrinsicState.State W E :=
  let q0 := q
  let q1 := PV_FN_THREAD_f361Chain130To139.after B q0
  let q2 := PV_FN_THREAD_f361Call459PostInit.after B H q1
  let q3 := PV_FN_THREAD_f361Chain140To142.after B q2
  let q4 := PV_FN_THREAD_f361Call279PostInit.after B H q3
  let q5 := PV_FN_THREAD_f361Chain143To144.after B q4
  let q6 := PV_FN_THREAD_f361Match144.after B K q5
  q6
/-- Source-only operational composition on the complete supplied store.
All native replies and interpretation gaps remain exact. No BODY is traversed.
This is not f361's own-entry contract or an argument-effect refinement. -/
theorem run {W E : Type} (B : Carrier W Data) (K : Control)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance B K programs H (steps B K H q) q = after B K H q := by
  unfold steps after
  dsimp only
  rw [PV_THR2_IntrinsicComposition.advance_add]
  rw [PV_FN_THREAD_f361Chain130To139.run B K programs H _]
  rw [PV_THR2_IntrinsicComposition.advance_add]
  rw [PV_FN_THREAD_f361Call459PostInit.run B K programs H _ (by rfl)]
  rw [PV_THR2_IntrinsicComposition.advance_add]
  rw [PV_FN_THREAD_f361Chain140To142.run B K programs H _]
  rw [PV_THR2_IntrinsicComposition.advance_add]
  rw [PV_FN_THREAD_f361Call279PostInit.run B K programs H _ (by rfl)]
  rw [PV_THR2_IntrinsicComposition.advance_add]
  rw [PV_FN_THREAD_f361Chain143To144.run B K programs H _]
  exact PV_FN_THREAD_f361Match144.run B K programs H _
#print axioms run
end PV_FN_THREAD_f361PostInitHead
namespace PV_FN_THREAD_f361ReturnedSuffix
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
def programs : Data → Option PV_STX2_SliceSyntax.Program := fun _ => none
def steps {W E : Type} (B : Carrier W Data) (K : Control)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) : Nat :=
  let q0 := q
  let q1 := PV_FN_THREAD_f361Chain145To149.after B q0
  let q2 := PV_FN_THREAD_f361Match149.after B K q1
  let q3 := PV_FN_THREAD_f361Chain150To155.after B q2
  let q4 := PV_FN_THREAD_f361Aggregate155.after B q3
  let q5 := PV_FN_THREAD_f361Chain156To159.after B q4
  let q6 := PV_FN_THREAD_f361Aggregate159.after B q5
  let q7 := PV_FN_THREAD_f361Chain160To187.after B q6
  let q8 := PV_FN_THREAD_f361Return.after B q7
  PV_FN_THREAD_f361Chain145To149.steps B q0 + (PV_FN_THREAD_f361Match149.steps B q1 + (PV_FN_THREAD_f361Chain150To155.steps B q2 + (PV_FN_THREAD_f361Aggregate155.steps B q3 + (PV_FN_THREAD_f361Chain156To159.steps B q4 + (PV_FN_THREAD_f361Aggregate159.steps B q5 + (PV_FN_THREAD_f361Chain160To187.steps B q6 + (PV_FN_THREAD_f361Return.steps B q7)))))))
def after {W E : Type} (B : Carrier W Data) (K : Control)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) : PV_THR2_IntrinsicState.State W E :=
  let q0 := q
  let q1 := PV_FN_THREAD_f361Chain145To149.after B q0
  let q2 := PV_FN_THREAD_f361Match149.after B K q1
  let q3 := PV_FN_THREAD_f361Chain150To155.after B q2
  let q4 := PV_FN_THREAD_f361Aggregate155.after B q3
  let q5 := PV_FN_THREAD_f361Chain156To159.after B q4
  let q6 := PV_FN_THREAD_f361Aggregate159.after B q5
  let q7 := PV_FN_THREAD_f361Chain160To187.after B q6
  let q8 := PV_FN_THREAD_f361Return.after B q7
  q8
/-- Source-only operational composition on the complete supplied store.
All native replies and interpretation gaps remain exact. No BODY is traversed.
This is not f361's own-entry contract or an argument-effect refinement. -/
theorem run {W E : Type} (B : Carrier W Data) (K : Control)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (q : PV_THR2_IntrinsicState.State W E) :
    PV_THR2_IntrinsicState.advance B K programs H (steps B K H q) q = after B K H q := by
  unfold steps after
  dsimp only
  rw [PV_THR2_IntrinsicComposition.advance_add]
  rw [PV_FN_THREAD_f361Chain145To149.run B K programs H _]
  rw [PV_THR2_IntrinsicComposition.advance_add]
  rw [PV_FN_THREAD_f361Match149.run B K programs H _]
  rw [PV_THR2_IntrinsicComposition.advance_add]
  rw [PV_FN_THREAD_f361Chain150To155.run B K programs H _]
  rw [PV_THR2_IntrinsicComposition.advance_add]
  rw [PV_FN_THREAD_f361Aggregate155.run B K programs H _]
  rw [PV_THR2_IntrinsicComposition.advance_add]
  rw [PV_FN_THREAD_f361Chain156To159.run B K programs H _]
  rw [PV_THR2_IntrinsicComposition.advance_add]
  rw [PV_FN_THREAD_f361Aggregate159.run B K programs H _]
  rw [PV_THR2_IntrinsicComposition.advance_add]
  rw [PV_FN_THREAD_f361Chain160To187.run B K programs H _]
  exact PV_FN_THREAD_f361Return.run B K programs H _
#print axioms run
end PV_FN_THREAD_f361ReturnedSuffix
