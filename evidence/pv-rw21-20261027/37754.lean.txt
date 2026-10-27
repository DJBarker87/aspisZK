import R1Z.ProverRw21ProofOutput
import R1Z.ProverRw21PackBytes
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw21ModelBytes
open Aeneas Aeneas.Std Result ProverRwFull
open ProverRw21ProtocolOutput ProverRw21ProofOutput

/-- Mathematical nodes and pure serialization determine the entire byte result;
this function contains no source execution or source-output projection. -/
def bytes (t : Transcript) : Result ProverRw19AuditData.ByteStatus :=
  ProverRw21PackBytes.pack (nodeResult t) (successful_length t)

theorem instance_bytes (t : Transcript) :
    ProverRw21ModelObservations.proofBytes (.ok (.Ok t))=bytes t := by
  rw [ProverRw21PackBytes.protocol_success,ProverRw21PackBytes.prepared_success]
  simp only [ProverRw21ProtocolOutput.prepared]
  rw [ProverRw21PackBytes.assembly]
  exact ProverRw21PackBytes.congr _ _ _ _ (reference_proof t)

theorem output (t : Transcript) :
    ProverRw21ModelInstance (.ok (.Ok t))=ProverRw19AuditData.attachAudit (bytes t) := by
  rw [ProverRw21ModelObservations.output,instance_bytes]

theorem rejected (t : Transcript) (e : ProverCommitPublish43.Error)
    (h : nodeResult t=.error e) :
    bytes t=.ok (.Err (ProverRw19MathematicalAssembly.error e)) :=
  ProverRw21PackBytes.rejected _ _ e h

theorem successful (t : Transcript) (raw : ProverCommitPublish43.Bytes)
    (h : nodeResult t=.ok raw) :
    ∃ proof : alloc.vec.Vec U8, bytes t=.ok (.Ok proof) ∧
      proof.val=raw.map ProverRw19MathematicalAssembly.byte :=
  ProverRw21PackBytes.successful _ _ raw h

#print axioms bytes
#print axioms instance_bytes
#print axioms output
#print axioms rejected
#print axioms successful
end R1Z.ProverRw21ModelBytes
