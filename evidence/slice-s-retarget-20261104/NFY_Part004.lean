import Lean
import NFY_Part002
import NFY_Part003

-- BEGIN copied NFD_WideSerialization: evidence/slice-s-compose10-20261104/NFD_WideSerialization.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NFD_WideSerialization
open Aeneas Aeneas.Std

def fromPort (x : NFY_NBG_WriterPorts.WE) : NFY_NBG_WriterPorts.NE :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
   ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩
theorem carrier_roundtrip (x : NFY_NBG_WriterPorts.NE) : fromPort (NFY_NBG_WriterPorts.port x)=x := rfl

/-- Same raw input, exact ordered bytes, complete returned value and empty frame.
The native iterator/window association is a separate hybrid certificate. -/
theorem result_state_effects {State : Type} (x : NFY_NBG_WriterPorts.NE) (state : State) :
    ∃ out, (AspisR1WideToBytesSource.field.wide_exact.WideExact.to_le_bytes
      (NFY_NBG_WriterPorts.port x),state,([] : List Unit)) = (Result.ok out,state,[]) ∧
      out.val = [x.c0.c0.a,x.c0.c0.b,x.c0.c1.a,x.c0.c1.b,
        x.c1.c0.a,x.c1.c0.b,x.c1.c1.a,x.c1.c1.b].flatMap
          (fun word => (core.num.U32.to_le_bytes word).val) := by
  obtain ⟨out,call,words⟩ := NFY_NBG_WriterPorts.writer_result x
  refine ⟨out,?_,?_⟩
  · rw [call]
  · exact words.trans (NFY_NBG_WriterPorts.word_order x)

#print axioms carrier_roundtrip
#print axioms result_state_effects
#print axioms AspisR1.NFY_NCA_SerializerWindow.frame
#print axioms AspisR1.NFY_NCA_SerializerWindow.induction
end NFY_NFD_WideSerialization
-- END copied NFD_WideSerialization

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
