import PV_FN_THREAD_f6Entry
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6Reply121
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine

/-- Only LEAF121 is abstracted here; structured124 is not excluded. -/
def programs (P : Data → Option PV_STX2_SliceSyntax.Program) (fn : Data) :=
  by classical exact if fn = PV_THR2_ScopeCall121.fn then none else P fn

/-- Source121 is not the higher-order intrinsic318, by emitted function id. -/
theorem not_intrinsic : PV_THR2_ScopeCall121.fn ≠ PV_THR2_Catch219Call318.fn := by
  intro eq
  have ids := congrArg PV_THR2_OffPath.functionId eq
  change (some 121 : Option Nat) = some 318 at ids
  cases ids

/-- Consume the complete arbitrary leaf reply at the ACTUAL first f6 request.
Nothing assumes success, a pure world, a fixed value or a fixed event suffix. -/
theorem full_reply {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : W) (es : List E) (stack : List Config) :
    let c := PV_THR2_ScopeCall121.pending s a parents
    let q := PV_THR2_ChildBoundary.delivered B c
      (PV_THR2_StaticReply.wait s PV_THR2_ScopeCall121.fn [.number 0] 5)
      (H (.child PV_THR2_ScopeCall121.fn s.nextActivation [.number 0]) w)
    PV_THR2_IntrinsicState.step B K (programs P) H ⟨⟨.running c,w,es⟩,stack⟩ =
      ⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩ := by
  dsimp only
  rw [PV_THR2_IntrinsicCompatible.step B K (programs P) H _ w es stack (by
    simp [PV_THR2_Catch316Segment.select,PV_THR2_ScopeCall121.pending,
      PV_THR2_StaticCall.pending,not_intrinsic])]
  have replyStep := PV_THR2_StaticReply.full_reply B K (programs P) H s a parents
    (PV_THR2_F6.live.body.drop 17) PV_THR2_ScopeCall121.fn [.number 0] 5 w
    (by simp [programs])
  change PV_THR2_Execution.step B K (programs P) H
    (PV_THR2_ScopeCall121.pending s a parents) w = _ at replyStep
  rw [replyStep]
  rfl

/-- Own-entry composition through the first arbitrary full reply. This is a
partial f6 result, not a row closure: all later calls and completion remain. -/
theorem from_entry {W E : Type} (base : Carrier W Data) (ctl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool) (w : W)
    (es : List E) (stack : List Config) :
    let B := PV_THR2_EntryDynamic.carrier
      (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier base)) b
    let t := PV_THR2_ScopePrologue.prepared s a
    let c := PV_THR2_ScopeCall121.pending t a parents
    let q := PV_THR2_ChildBoundary.delivered B c
      (PV_THR2_StaticReply.wait t PV_THR2_ScopeCall121.fn [.number 0] 5)
      (H (.child PV_THR2_ScopeCall121.fn t.nextActivation [.number 0]) w)
    PV_THR2_IntrinsicState.advance B (PV_THR2_Scalars.control ctl) (programs P) H 18
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body},parents,s⟩,w,es⟩,stack⟩ =
      ⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩ := by
  dsimp only
  rw [show 18 = 17 + 1 from rfl,PV_THR2_IntrinsicComposition.advance_add,
    PV_FN_THREAD_f6Entry.request base ctl (programs P) H s a parents b w es stack]
  simp only [PV_THR2_IntrinsicState.advance]
  exact full_reply _ _ P H _ a parents w es stack

#print axioms not_intrinsic
#print axioms full_reply
#print axioms from_entry
end PV_FN_THREAD_f6Reply121
