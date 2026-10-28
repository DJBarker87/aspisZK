import NDO_JHb_Emit
import NDO_JGx_RealStatement
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHb_EmitAdapter
open Aeneas Aeneas.Std Result
/-- Explicit return-data runtime model. It records the emitted bytes/events;
it is not a native syscall refinement or a constant-success emit_result. -/
def runtime : S2I.ReturnData.State Unit Unit → List U8 → Result (S2I.ReturnData.State Unit Unit) :=
  fun state bytes=>ok (S2I.ReturnData.set state bytes)

theorem runtime_law : S2I.ReturnData.RuntimePremise runtime := fun _ _=>rfl
#print axioms runtime_law

def source (statement : AspisS6CurrentCodecInstallation.Statement) :
    Result (core.result.Result Unit AdapterRw.solana_program_error.ProgramError) := do
  let result ← JHb_Emit.source runtime ⟨(),[],[]⟩
    (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 statement)
  match result with
  | .Err e=>ok (.Err e)
  | .Ok _=>ok (.Ok ())

theorem accepted : source JGx_RealStatement.value=ok (.Ok ()) := by
  unfold source JGx_RealStatement.value
  rw [AspisS6CurrentAdapterCarrier.to_fromPoolV1PairForestTerminalStatementV1]
  rw [JHb_Emit.real runtime runtime_law,bind_tc_ok]
#print axioms accepted
end AspisR1.JHb_EmitAdapter
end
