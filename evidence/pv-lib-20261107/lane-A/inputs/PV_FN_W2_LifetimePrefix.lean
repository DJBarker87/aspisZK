import PV_THR2_IntrinsicFrameSteps
set_option autoImplicit false
namespace PV_FN_W2_LifetimePrefix
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
abbrev Operation := Site × Bool × Nat
def node (op : Operation) : PV_STX2_SliceSyntax.Node := .leaf (.storage op.1 op.2.1 op.2.2)
def store (s : Store Data) (a : Nat) (ops : List Operation) : Store Data :=
  ops.foldl (fun t op => write t ⟨a,op.2.2,[]⟩ none) s
/-- Symbolic lifetime-prefix composition. The remainder is never unfolded,
and no source call, native reply, or loop body is evaluated. -/
theorem run {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (ops : List Operation) (s : Store Data) (a : Nat) (parents : List Frame)
    (loops : List LoopFrame) (rest : List PV_STX2_SliceSyntax.Node)
    (w : W) (es : List E) (stack : List Config) :
    PV_THR2_IntrinsicState.advance B K P H ops.length
      ⟨⟨.running ⟨{activation := a,remaining := ops.map node ++ rest,loops := loops},parents,s⟩,w,es⟩,stack⟩ =
      ⟨⟨.running ⟨{activation := a,remaining := rest,loops := loops},parents,store s a ops⟩,w,es⟩,stack⟩ := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    rw [List.length_cons,Nat.add_comm ops.length 1]
    change PV_THR2_IntrinsicState.advance B K P H (1+ops.length)
      ⟨⟨.running ⟨{activation := a,remaining := node op :: (ops.map node ++ rest),loops := loops},parents,s⟩,w,es⟩,stack⟩ = _
    rw [PV_THR2_IntrinsicComposition.advance_add]
    rw [show PV_THR2_IntrinsicState.advance B K P H 1
      ⟨⟨.running ⟨{activation := a,remaining := node op :: (ops.map node ++ rest),loops := loops},parents,s⟩,w,es⟩,stack⟩ =
      ⟨⟨.running ⟨{activation := a,remaining := ops.map node ++ rest,loops := loops},parents,
        write s ⟨a,op.2.2,[]⟩ none⟩,w,es⟩,stack⟩ from
      PV_THR2_IntrinsicFrameSteps.storage B K P H s a parents loops _ op.1 op.2.1 op.2.2 w es stack]
    exact ih (write s ⟨a,op.2.2,[]⟩ none)
#print axioms run
end PV_FN_W2_LifetimePrefix
