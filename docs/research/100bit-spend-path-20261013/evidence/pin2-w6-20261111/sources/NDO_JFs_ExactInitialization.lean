import NDO_JFs_ExactSerialization
import NDO_JFu_OracleSeed
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFs_ExactInitialization
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/- PIN2 W6: the PIN2 `public_transcript` of `toPIN2 JFs_PublicSerialization.value` under the
   installed oracle (carried by `pin2Digest`); length word 1520 (was 1455). -/
theorem source {Hash : Type} (H : Bytes → State)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (root : Array U8 32#usize) :
    AspisR1PublicPreparationPIN2.r1_semantic.public_transcript
      (PIN2W6_TranscriptSeed.pin2Digest
        (AspisR1CurrentCaller.InstalledPreparation.retainedDigest (F3V_OracleDictionary.current H D)))
      (PreparationBinding.toPIN2 JFs_PublicSerialization.value) hash root=ok (.Ok
        (⟨MultiproofConePhysicalTransport.rawOracle H
          (TranscriptStep.initParts (alloc.vec.Vec.deref JFs_ExactSerialization.encoded) root 1520#u32),
          hash,0#u8⟩ : AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript Hash)) :=
  JFu_OracleSeed.source H D hash _ JFs_ExactSerialization.encoded JFs_ExactSerialization.source
    JFs_ExactSerialization.length root

#print axioms source
end AspisR1.JFs_ExactInitialization
end
