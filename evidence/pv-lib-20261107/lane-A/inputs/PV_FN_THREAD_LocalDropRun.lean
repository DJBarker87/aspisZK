import PV_FN_THREAD_LocalDrop
set_option autoImplicit false
namespace PV_FN_THREAD_LocalDropRun
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_FN_THREAD_LocalDrop
/-- Complete source Drop boundary. An absent conditional value skips the
request; an absent unconditional value retains the source gap. All full reply
branches, the native post-world, and the source store are kept exactly. -/
theorem run {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (a slot : Nat) (parents : List Frame) (loops : List LoopFrame)
    (rest : List PV_STX2_SliceSyntax.Node) (site : Site) (fn : Data) (conditional : Bool)
    (w : W) (es : List E) (stack : List Config) :
    PV_THR2_IntrinsicState.advance B K P H (steps B s a slot)
      ⟨⟨.running ⟨{activation := a,remaining := .leaf (.drop site (.local slot) fn conditional []) :: rest,loops := loops},parents,s⟩,w,es⟩,stack⟩ =
      after B H s a slot parents loops rest site fn conditional w es stack := by
  cases cell : s.cells ⟨a,slot,[]⟩ with
  | none =>
    cases conditional <;>
      simp [steps,after,cell,PV_THR2_IntrinsicState.advance,PV_THR2_IntrinsicState.step,
        PV_THR2_Catch316Segment.select,PV_THR2_Execution.step,PV_THR2_Dynamic.active,
        PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,
        PV_STX2_SliceMachine.step,native,adopt,PV_STX2_Native.step,PV_STX2_Store.read]
  | some value =>
    simp only [steps,cell]
    rw [PV_THR2_IntrinsicComposition.advance_add,
      issue B K P H s a slot parents loops rest site fn value conditional w es stack cell,
      receive]
    simp only [after,cell]
#print axioms run
end PV_FN_THREAD_LocalDropRun
