import PV_FN_THREAD_f6PostStore
import PV_FN_THREAD_f6CounterBranches
import PV_FN_THREAD_f6FlagRequest
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6ReturnedContinuations
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine

def resumed (post : Store Data) (child a dest : Nat) (v : Data) :=
  write (write post ⟨child,0,[]⟩ (some v)) ⟨a,dest,[]⟩ (some v)

/-- The reference is the value of126's returned Post branch. No root-cell or
pointee premise is added: actual return administration derives LOCAL17. -/
theorem after2097 {W E : Type} (base : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (post : Store Data) (child a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (b : Bool) (p : Address) (w : W) (es : List E) (stack : List Config) :
    let t := resumed post child a 17 (PV_STX2_TypedReferences.reference p .null)
    PV_THR2_IntrinsicState.advance (PV_FN_THREAD_f6CounterTest.carrier base b) ctl P H 5
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.block86.drop 7,loops := loops},parents,t⟩,w,es⟩,stack⟩ =
      ⟨⟨.running (PV_FN_THREAD_f6LoadCounter.pending t a parents loops p),w,es⟩,stack⟩ := by
  dsimp only
  rw [PV_FN_THREAD_f6OperatorCarrier.agreement]
  exact PV_FN_THREAD_f6LoadCounter.run _ ctl P H _ a parents loops b p w es stack
    (PV_FN_THREAD_f6PostStore.destination _ child a 17 _)

theorem after2306 {W E : Type} (base : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (post : Store Data) (child a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (b : Bool) (p : Address) (w : W) (es : List E) (stack : List Config) :
    let t := resumed post child a 22 (PV_STX2_TypedReferences.reference p .null)
    PV_THR2_IntrinsicState.advance (PV_FN_THREAD_f6CounterTest.carrier base b) ctl P H 3
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.block86.drop 24,loops := loops},parents,t⟩,w,es⟩,stack⟩ =
      ⟨⟨.running (PV_FN_THREAD_f6ParkRequest.pending t a parents loops p),w,es⟩,stack⟩ := by
  dsimp only
  rw [PV_FN_THREAD_f6OperatorCarrier.agreement]
  exact PV_FN_THREAD_f6ParkRequest.run _ ctl P H _ a parents loops b p w es stack
    (PV_FN_THREAD_f6PostStore.destination _ child a 22 _)

theorem after2197_zero {W E : Type} (base : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (post : Store Data) (child a : Nat) (parents : List Frame)
    (afterLoop : List PV_STX2_SliceSyntax.Node) (lower : List LoopFrame)
    (b : Bool) (w : W) (es : List E) (stack : List Config) :
    let t := resumed post child a 15 (.number 0)
    PV_THR2_IntrinsicState.advance (PV_FN_THREAD_f6CounterTest.carrier base b) ctl P H 5
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.block86.drop 12,loops := ⟨PV_THR2_F6.block86,afterLoop⟩ :: lower},parents,t⟩,w,es⟩,stack⟩ =
      ⟨⟨.running ⟨{activation := a,remaining := afterLoop,loops := lower},parents,
        write (PV_FN_THREAD_f6CounterTest.prepared t a 0) ⟨a,14,[]⟩ none⟩,w,es⟩,stack⟩ := by
  exact PV_FN_THREAD_f6CounterBranches.zero_exit base ctl P H _ a parents afterLoop
    lower b w es stack (PV_FN_THREAD_f6PostStore.destination _ child a 15 _)

theorem after2404 {W E : Type} (B : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (post : Store Data) (child a : Nat) (parents : List Frame)
    (loop : LoopFrame) (lower : List LoopFrame) (v : Data)
    (w : W) (es : List E) (stack : List Config) :
    let t := resumed post child a 20 v
    PV_THR2_IntrinsicState.advance B ctl P H 5
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.block86.drop 27,loops := loop :: lower},parents,t⟩,w,es⟩,stack⟩ =
      ⟨⟨.running ⟨{activation := a,remaining := loop.body,loops := loop :: lower},
        parents,PV_FN_THREAD_f6LoopBack.prepared t a⟩,w,es⟩,stack⟩ := by
  exact PV_FN_THREAD_f6LoopBack.run B ctl P H _ a parents loop lower w es stack

theorem after2659 {W E : Type} (base : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (post : Store Data) (child a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (b : Bool) (p : Address) (w : W) (es : List E) (stack : List Config) :
    let t := resumed post child a 30 (PV_STX2_TypedReferences.reference p .null)
    PV_THR2_IntrinsicState.advance (PV_FN_THREAD_f6CounterTest.carrier base b) ctl P H 5
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body.drop 62,loops := loops},parents,t⟩,w,es⟩,stack⟩ =
      ⟨⟨.running (PV_FN_THREAD_f6FlagRequest.pending t a parents loops p),w,es⟩,stack⟩ := by
  dsimp only
  rw [PV_FN_THREAD_f6OperatorCarrier.agreement]
  exact PV_FN_THREAD_f6FlagRequest.run _ ctl P H _ a parents loops b p w es stack
    (PV_FN_THREAD_f6PostStore.destination _ child a 30 _)

#print axioms after2097
#print axioms after2306
#print axioms after2197_zero
#print axioms after2404
#print axioms after2659
end PV_FN_THREAD_f6ReturnedContinuations
