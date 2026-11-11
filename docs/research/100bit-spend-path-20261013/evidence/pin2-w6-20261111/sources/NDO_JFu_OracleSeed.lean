import NDO_JFu_TranscriptLength
import RPz7_F3V_OracleDictionary
import PIN2W6_TranscriptSeed
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFu_OracleSeed
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/- PIN2 W6: stated on the PIN2 emission of `r1_semantic::public_transcript` (Stream C,
   `PIN2_NEWGATE_r1_semantic`): `pub` is a PIN2 carrier and `serialized` its PIN2
   `public_bytes`; the installed oracle dictionary is carried to the PIN2 Digest32 type
   field for field (`PIN2W6_TranscriptSeed.pin2Digest`, same `digest`); the size premise
   and the length word are 1520 (were 1455).  The returned transcript is the PIN2
   `SemanticTranscript` with the same three fields. -/
theorem source {Hash : Type} (H : Bytes → State)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub : AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public) (encoded : alloc.vec.Vec U8)
    (serialized : AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes pub=
      ok (.Ok encoded))
    (size : encoded.val.length=1520) (root : Array U8 32#usize) :
    let D0 := PIN2W6_TranscriptSeed.pin2Digest
      (AspisR1CurrentCaller.InstalledPreparation.retainedDigest (F3V_OracleDictionary.current H D))
    AspisR1PublicPreparationPIN2.r1_semantic.public_transcript D0 pub hash root=ok (.Ok
      (⟨MultiproofConePhysicalTransport.rawOracle H
        (TranscriptStep.initParts (alloc.vec.Vec.deref encoded) root 1520#u32),hash,0#u8⟩ :
        AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript Hash)) := by
  exact PIN2W6_TranscriptSeed.public_source _ hash pub encoded serialized root 1520#u32
    (PIN2W6_TranscriptSeed.converted _ size) _ rfl

#print axioms source
end AspisR1.JFu_OracleSeed
end
