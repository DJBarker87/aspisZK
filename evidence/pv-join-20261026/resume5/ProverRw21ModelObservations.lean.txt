import R1Z.ProverRw21ModelInstance
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw21ModelObservations
open Aeneas Aeneas.Std Result ProverRwFull
abbrev Protocol := Result (core.result.Result ProverRw21ProtocolOutput.Transcript verifier.Error)

def preparation (protocol : Protocol) : ProverRw19PreparedAssembly.Preparation := do
  let status ← protocol
  match status with
  | .Err error => ok (.Err error)
  | .Ok t => ok (.Ok (ProverRw21ProtocolOutput.prepared t))

def proofBytes (protocol : Protocol) : Result ProverRw19AuditData.ByteStatus :=
  ProverRw19PreparedAssembly.proofBytes (preparation protocol)

theorem output (protocol : Protocol) :
    ProverRw21ModelInstance protocol = ProverRw19AuditData.attachAudit (proofBytes protocol) := rfl

theorem bytes (protocol : Protocol) :
    PV_RW_DataProduct.observe PV_RW_DataProduct.first (ProverRw21ModelInstance protocol) = proofBytes protocol :=
  ProverRw19AuditData.bytes _

theorem failure (error : Aeneas.Std.Error) : ProverRw21ModelInstance (.fail error) = .fail error := rfl
theorem divergence : ProverRw21ModelInstance .div = .div := rfl
theorem rejected (error : verifier.Error) : ProverRw21ModelInstance (.ok (.Err error)) = .ok (.Err error) := rfl

theorem length (protocol : Protocol) :
    ProverRw19ByteLength.HasLength 57607 (proofBytes protocol) :=
  ProverRw19PreparedAssembly.length _

#print axioms preparation
#print axioms proofBytes
#print axioms output
#print axioms bytes
#print axioms failure
#print axioms divergence
#print axioms rejected
#print axioms length
end R1Z.ProverRw21ModelObservations
