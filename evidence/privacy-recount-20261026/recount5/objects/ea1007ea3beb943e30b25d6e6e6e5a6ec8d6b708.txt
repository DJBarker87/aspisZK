import R1Z.ProverRw21ProtocolOutput
set_option autoImplicit false
noncomputable section
namespace R1Z
open Aeneas Aeneas.Std Result ProverRwFull

/-- Stable mathematical serialization instance. Its input is mathematical
protocol data, never a projection of a source output. The deployed-input to
Transcript construction is a separate, still open obligation. This declaration
must not be reported as discharging that construction. -/
def ProverRw21ModelInstance
    (protocol : Result (core.result.Result ProverRw21ProtocolOutput.Transcript verifier.Error)) :
    Result ProverRw19AuditValue.Status :=
  ProverRw19PreparedAssembly.output (do
    let status ← protocol
    match status with
    | .Err error => ok (.Err error)
    | .Ok transcript => ok (.Ok (ProverRw21ProtocolOutput.prepared transcript)))

#print axioms ProverRw21ModelInstance
end R1Z
