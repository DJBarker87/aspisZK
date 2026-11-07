import PV_FN_THREAD_f6ParkDeref
import PV_FN_THREAD_f6ParkRequest
import PV_FN_THREAD_f6LoopEntry
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6LoopReplies
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine

/-- Static call boundary with its actual saved loop stack. The arbitrary full
reply is delivered once; no callee body or return-value restriction is present. -/
theorem full_reply {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (rest : List PV_STX2_SliceSyntax.Node) (fn : Data) (vs : List Data) (dest : Nat)
    (w : W) (es : List E) (stack : List Config)
    (child : P fn = none) (ordinary : fn ≠ PV_THR2_Catch219Call318.fn) :
    let c := PV_THR2_StaticCall.pending s a parents rest fn vs dest
    let c := {c with frame := {c.frame with loops := loops}}
    let q := PV_THR2_ChildBoundary.delivered B c
      (PV_THR2_StaticReply.wait s fn vs dest) (H (.child fn s.nextActivation vs) w)
    PV_THR2_IntrinsicState.step B K P H ⟨⟨.running c,w,es⟩,stack⟩ =
      ⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩ := by
  dsimp only
  rw [PV_THR2_IntrinsicCompatible.step B K P H _ w es stack (by
    rcases vs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, tail⟩⟩⟩⟩ <;>
      simp [PV_THR2_Catch316Segment.select,PV_THR2_StaticCall.pending,ordinary]),
    PV_THR2_ExecutionBoundary.full_reply B K P H _ _ fn s.nextActivation dest vs w
      rfl rfl rfl rfl child]
  rfl

/-- Success is one branch of that same reply rule. Both the return value and
world/event suffix remain arbitrary; the loop stack and explicit store survive. -/
theorem returned {W E : Type} (B : Carrier W Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (rest : List PV_STX2_SliceSyntax.Node) (fn : Data) (vs : List Data) (dest : Nat)
    (v : Data) (w : W) (es : List E) :
    let c := PV_THR2_StaticCall.pending s a parents rest fn vs dest
    let c := {c with frame := {c.frame with loops := loops}}
    PV_THR2_ChildBoundary.delivered B c (PV_THR2_StaticReply.wait s fn vs dest)
      ⟨.returned (.ok v),w,es⟩ =
      ⟨.running ⟨{activation := a,remaining := rest,loops := loops},parents,
        PV_THR2_StaticReply.returnedStore s a vs dest v⟩,w,es⟩ := rfl

#print axioms full_reply
#print axioms returned
end PV_FN_THREAD_f6LoopReplies
