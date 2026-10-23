import S2W_AuthenticatedInputs
import OraclePortCheckpointResumeC5

/-! Fixed C5 digest-field decoder: proof digest at 16, public digest at 48.
This decodes the two saved digests only; successful child execution owns the
remaining frame checks. No user-selected decoder is a parameter. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.ChildJoin_Decoder
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical OraclePortCheckpointAbiC5 OraclePortCompactDraft

def digest (b : Bytes) : Option State :=
  if b.length = 32 then some (fun j => b[j.val]?.getD 0) else none

def checkpointHeader : S2W_AuthenticatedInputs.HeaderDecode := fun ck => do
  let hp ← digest (slice ck 16 32)
  let hu ← digest (slice ck 48 32)
  pure (hp,hu)

theorem digest_bytes (s : State) : digest (bytes s) = some s := by
  unfold digest
  rw [show (bytes s).length = 32 by simp [bytes], if_pos rfl]
  congr 1
  funext j
  simp [bytes, j.isLt]

theorem encoded_header (H : Bytes → State) (proof public1 : Bytes)
    (p : Prepared) (a : QueryAccumulator.State K E) :
    checkpointHeader (encode H proof public1 p a) = some (H proof,H public1) := by
  have hp := OraclePortCheckpointSlicesC5.field_at H proof public1 p a 1 16 32
    (bytes (H proof)) rfl rfl rfl (by decide)
  have hu := OraclePortCheckpointSlicesC5.field_at H proof public1 p a 2 48 32
    (bytes (H public1)) rfl rfl rfl (by decide)
  simp only [checkpointHeader,hp,hu,digest_bytes,Option.bind_some,pure]

#print axioms digest_bytes
#print axioms encoded_header
end AspisR1.ChildJoin_Decoder
end
