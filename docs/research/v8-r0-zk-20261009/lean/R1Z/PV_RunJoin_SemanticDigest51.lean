import R1Z.PV_RunJoin_SemanticRequests51
import R1Z.PV_RunJoin_TranscriptDigest51
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SemanticDigest51
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46

theorem source (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (t : host_wire.SemanticTranscript aspis_core.digest.LegacyHashFn) (row : U8) (framed : Slice U8) :
    @host_wire.SemanticTranscript.sample_block_validated (types base) _
      (@aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 (types base) (selected base heap box ops))
      t row framed=
      if row != t.next_row then ok (core.result.Result.Err (r1_wire.Error.RowOrder t.next_row row),t) else (do
        let absorbed ← t.hash (PV_RunJoin_SemanticRequests51.request t.state row framed)
        let b ← t.hash (PV_RunJoin_TranscriptRequests51.message absorbed 1#u8)
        let advanced ← t.hash (PV_RunJoin_TranscriptRequests51.message absorbed 2#u8)
        ok (core.result.Result.Ok b,{t with state:=advanced,next_row:=U8.wrapping_add t.next_row 1#u8})) := by
  rw [PV_RunJoin_SemanticRequests51.source]
  simp only [aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32,PV_RunJoin_TranscriptDigest51.installed]
#print axioms source
end R1Z.PV_RunJoin_SemanticDigest51
