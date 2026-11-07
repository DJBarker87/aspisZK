import PV_FN_THREAD_f6RequestQuiet
set_option autoImplicit false
namespace PV_FN_THREAD_f6CompletionReselection
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine

/-- The actual emitted catch318 caller, after non-success has propagated into
it. Adoption retains its waiting request when marking completion. -/
def completedCatch (s : Store Data) (a : Nat) (parents : List Frame) : Config :=
  let c := PV_THR2_Catch219Call318.pending s a parents
  {c with frame := {c.frame with completed := some .div}}

/-- A completed divergence is Quiet according to the accepted source-only
helper. No successful reply or newly chosen callback is involved. -/
theorem quiet (s : Store Data) (a : Nat) (parents : List Frame) :
    PV_FN_THREAD_f6RequestQuiet.Quiet (.running (completedCatch s a parents)) := by
  exact ⟨.div,rfl,by intro value h; cases h⟩

/-- The higher-order selector ignores completed. It selects the actual316
callback again even on this completed divergence. -/
theorem selected (s : Store Data) (a : Nat) (parents : List Frame) :
    PV_THR2_Catch316Segment.select (completedCatch s a parents) =
      some (PV_THR2_CallbackSegment.enter (completedCatch s a parents)
        PV_THR2_F316.live [PV_STX2_TypedReferences.reference ⟨a,2,[]⟩ .null]) := by
  simp [PV_THR2_Catch316Segment.select,completedCatch,
    PV_THR2_Catch219Call318.pending,PV_THR2_StaticCall.pending,
    PV_THR2_Catch219Call318.args]

/-- Full IntrinsicState execution enters316, adding a suspended caller,
rather than propagating divergence. This is independent of every machine
component and every native reply. It includes the actual dynamic/completion
wrapper, not merely the source step relation. -/
theorem reentered {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (w : W) (es : List E)
    (stack : List Config) :
    PV_THR2_IntrinsicState.step B K P H
      ⟨⟨.running (completedCatch s a parents),w,es⟩,stack⟩ =
    PV_THR2_IntrinsicState.invoke
      ⟨⟨.running (completedCatch s a parents),w,es⟩,stack⟩
      (PV_THR2_CallbackSegment.enter (completedCatch s a parents)
        PV_THR2_F316.live [PV_STX2_TypedReferences.reference ⟨a,2,[]⟩ .null]) := by
  simp only [PV_THR2_IntrinsicState.step,selected]

/-- In particular the source Quiet invariant is false after this real
IntrinsicState transition. A source-only quiet lemma cannot supply the missing
all-step control induction. -/
theorem quiet_not_preserved {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (w : W) (es : List E)
    (stack : List Config) :
    ¬ PV_FN_THREAD_f6RequestQuiet.Quiet
      (PV_THR2_IntrinsicState.step B K P H
        ⟨⟨.running (completedCatch s a parents),w,es⟩,stack⟩).current.status := by
  rw [reentered]
  intro h
  rcases h with ⟨r,done,_⟩
  cases done

#print axioms quiet
#print axioms selected
#print axioms reentered
#print axioms quiet_not_preserved
end PV_FN_THREAD_f6CompletionReselection
