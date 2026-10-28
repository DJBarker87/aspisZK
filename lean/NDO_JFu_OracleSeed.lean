import NDO_JFu_TranscriptLength
import RPz7_F3V_OracleDictionary
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFu_OracleSeed
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem source {Hash : Type} (H : Bytes → State)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (encoded : alloc.vec.Vec U8)
    (serialized : pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes pub=ok (.Ok encoded))
    (size : encoded.val.length=1455) (root : Array U8 32#usize) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest (F3V_OracleDictionary.current H D)
    r1_semantic.public_transcript D0 pub hash root=ok (.Ok
      (⟨MultiproofConePhysicalTransport.rawOracle H
        (TranscriptStep.initParts (alloc.vec.Vec.deref encoded) root 1455#u32),hash,0#u8⟩ : r1_wire.SemanticTranscript Hash)) := by
  exact JFu_TranscriptSeed.public_source _ hash pub encoded serialized root 1455#u32
    (JFu_TranscriptLength.converted _ size) _ rfl

#print axioms source
end AspisR1.JFu_OracleSeed
end
