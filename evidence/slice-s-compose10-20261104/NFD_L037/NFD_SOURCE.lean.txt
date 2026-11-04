import NBG_WriterPorts
import NCA_SerializerWindow
set_option autoImplicit false
noncomputable section
namespace NFD_WideSerialization
open Aeneas Aeneas.Std

def fromPort (x : NBG_WriterPorts.WE) : NBG_WriterPorts.NE :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
   ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩
theorem carrier_roundtrip (x : NBG_WriterPorts.NE) : fromPort (NBG_WriterPorts.port x)=x := rfl

/-- Same raw input, exact ordered bytes, complete returned value and empty frame.
The native iterator/window association is a separate hybrid certificate. -/
theorem result_state_effects {State : Type} (x : NBG_WriterPorts.NE) (state : State) :
    ∃ out, (AspisR1WideToBytesSource.field.wide_exact.WideExact.to_le_bytes
      (NBG_WriterPorts.port x),state,([] : List Unit)) = (Result.ok out,state,[]) ∧
      out.val = [x.c0.c0.a,x.c0.c0.b,x.c0.c1.a,x.c0.c1.b,
        x.c1.c0.a,x.c1.c0.b,x.c1.c1.a,x.c1.c1.b].flatMap
          (fun word => (core.num.U32.to_le_bytes word).val) := by
  obtain ⟨out,call,words⟩ := NBG_WriterPorts.writer_result x
  refine ⟨out,?_,?_⟩
  · rw [call]
  · exact words.trans (NBG_WriterPorts.word_order x)

#print axioms carrier_roundtrip
#print axioms result_state_effects
#print axioms AspisR1.NCA_SerializerWindow.frame
#print axioms AspisR1.NCA_SerializerWindow.induction
end NFD_WideSerialization
