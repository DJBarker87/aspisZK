import CheckpointBytesDecodeC5

set_option autoImplicit false
noncomputable section
namespace AspisR1.CheckpointBytesBodyDecodeJoin
open Aeneas Aeneas.Std Result
open OraclePortCkptAbi2Extracted aspis_r1_cost_probe.verifier
open CheckpointBytesBody CheckpointBytesBlocks CheckpointBytesDigest CheckpointBytesDecodeC5
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortCompactDraft

def checkpoint (H : Bytes → State) (p : Prepared) (a : Accumulator)
    (hp hu : Array U8 32#usize) : Bytes :=
  let b := sourceBody p a hp hu
  b ++ bytes (H (OraclePortPhysicalFrameDraft.domain ++ b))

/-- Concrete selector materialization and complete-body checksum feed the
strict C5 decoder. Proof/public digest equality belongs to caller binding.
The result retains duplicate query rejection and assumes no allocation. -/
theorem decode_checkpoint (H : Bytes → State) (stored pub : Bytes)
    (p : Prepared) (a : Accumulator) (hp hu : Array U8 32#usize)
    (size : a.weights.val.length = 64)
    (qb : ∀ j : Fin 22, (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val < 262144)
    (canonical : CanonicalFields (fields p a size qb)) (next : a.next.val = 10)
    (proofHash : stateOf hp = H stored) (publicHash : stateOf hu = H pub) :
    OraclePortCkptAbiCodec.decode (checkpoint H p a hp hu) =
      if Function.Injective (fields p a size qb).queries then
        some (prepared (fields p a size qb) canonical,accumulator (fields p a size qb) canonical)
      else none := by
  have encoding : checkpoint H p a hp hu =
      OraclePortCheckpointAbiC5.encode H stored pub
        (prepared (fields p a size qb) canonical) (accumulator (fields p a size qb) canonical) := by
    unfold checkpoint
    rw [source_body_c5 p a hp hu size qb canonical next,proofHash,publicHash]
    rfl
  rw [encoding]
  exact decode_source_fields H stored pub p a size qb canonical

#print axioms decode_checkpoint
end AspisR1.CheckpointBytesBodyDecodeJoin
end
