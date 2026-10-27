import JFs_PublicSerialization
import JFs_SourceProjection
import JFu_OracleSeed
import JFu_InitializedTrace
import JFv_OracleTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFs_InitializedPublic
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem source {Hash : Type} (H : Bytes → State)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) :
    ∃ encoded : alloc.vec.Vec U8,
      pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes JFs_PublicSerialization.value=ok (.Ok encoded) ∧
      encoded.val.length=1455 ∧
      r1_semantic.public_transcript
        (AspisR1CurrentCaller.InstalledPreparation.retainedDigest (F3V_OracleDictionary.current H D))
        JFs_PublicSerialization.value hash root=ok (.Ok
          (⟨MultiproofConePhysicalTransport.rawOracle H
            (TranscriptStep.initParts (alloc.vec.Vec.deref encoded) root 1455#u32),hash,0#u8⟩ : r1_wire.SemanticTranscript Hash)) := by
  obtain ⟨encoded,serialized,contents,length⟩:=JFs_PublicSerialization.source
  exact ⟨encoded,serialized,length,JFu_OracleSeed.source H D hash _ encoded serialized length root⟩

#print axioms source
end AspisR1.JFs_InitializedPublic
end
