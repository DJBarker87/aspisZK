import RPt_FJl_ReaderCanonical
import CheckpointBytes4Layout
import F3L_WriterNumeric
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_ReaderGamma
open Aeneas Aeneas.Std Result AspisR1Stage2
open OraclePortCompactDraft MultiproofConeCanonical
/-- Strict literal gamma decode from the SAME successful reader. -/
theorem value (reserved : Bool) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (checkpoint proof pub : Slice U8) (hash : Hash) (p : verifier.Prepared) (a : verifier.Accumulator)
    (run : verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved) D checkpoint proof pub .S2 hash=ok (.Ok (p,a))) :
    FoldedLeafCodec.decodeWide (slice (bytesOf checkpoint.val) 176 32)=
      some (CheckpointBytes5Output.ofE p.gamma) := by
  obtain ⟨f⟩ := CheckpointBytes4Ops.successful_fields reserved D checkpoint proof pub .S2 hash p a run
  obtain ⟨_,_,_,_,_,length,_⟩ := Tx2N_Header.cuts reserved D checkpoint proof pub hash p a run
  have flat := CheckpointBytes4Layout.flat_fields reserved checkpoint p a f length
  obtain ⟨gamma,decoded,same⟩ := flat.gamma
  rw [←same,CheckpointBytes5Output.ofE_source]
  exact decoded
#print axioms value
end AspisR1.FJo_ReaderGamma
end
