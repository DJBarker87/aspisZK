import PV_THR2_IntrinsicStructuredCall
set_option autoImplicit false
namespace PV_THR2_PacketStructuredOneArg
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
/-- Conditional on amended-translator acceptance. Hypothesis: actual source
argument cell. Source move binds that precise value to a fresh callee; no
reference, alias or returned-value premise. -/
theorem after {W E : Type} (B : Carrier W Data) (s : Store Data) (a src dest : Nat)
    (parents : List Frame) (loops : List LoopFrame) (rest : List PV_STX2_SliceSyntax.Node)
    (site : Site) (fn value : Data) (body : PV_STX2_SliceSyntax.Program)
    (w : W) (es : List E) (stack : List Config)
    (cell : s.cells ⟨a,src,[]⟩ = some value) :
    PV_THR2_IntrinsicStructuredCall.after B s a parents loops rest site fn
      [.move (.local src)] dest body w es stack =
    ⟨⟨.running (PV_THR2_IntrinsicFrameEnter.entered
      (write s ⟨a,src,[]⟩ none) a parents loops rest fn [value] dest body),w,es⟩,stack⟩ := by
  have selected : operands B w a [.move (.local src)] s =
      some ([value],write s ⟨a,src,[]⟩ none) := by
    simp [operands,operand,PV_STX2_Store.read,locate,readAddress,readFields,writeAddress,cell]
  simp only [PV_THR2_IntrinsicStructuredCall.after,selected]
/-- The derived fresh activation has precisely the moved source argument. -/
theorem argument (s : Store Data) (a dest : Nat) (parents : List Frame)
    (loops : List LoopFrame) (rest : List PV_STX2_SliceSyntax.Node)
    (fn value : Data) (body : PV_STX2_SliceSyntax.Program) :
    let c := PV_THR2_IntrinsicFrameEnter.entered s a parents loops rest fn [value] dest body
    c.store.cells ⟨c.frame.activation,1,[]⟩ = some value := by
  simp [PV_THR2_IntrinsicFrameEnter.entered,PV_THR2_IntrinsicFrameEnter.pending,
    PV_THR2_StaticCall.issued,PV_STX2_Native.arguments,write]
#print axioms after
#print axioms argument
end PV_THR2_PacketStructuredOneArg
