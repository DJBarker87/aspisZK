import NDO_JFp_Query00Absorb
import NDO_JFp_Query00Read
import NDO_JFp_Query00Ratchet
import NDO_JFp_SHADigest
import NDO_JFw_NativeRow00
set_option autoImplicit false
namespace AspisR1.JFp_Query00Source
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

def frame : Slice U8 := ⟨[0#u8,0#u8,0#u8,0#u8,0#u8],by scalar_tac⟩
def absorbed : State := JFp_SHADigest.output JFp_Query00Absorb.result
def block : State := JFp_SHADigest.output JFp_Query00Read.result
def ratchet : State := JFp_SHADigest.output JFp_Query00Ratchet.result

theorem realFrame : JFw_NativeRow00.record=frame := by
  apply Subtype.ext
  rfl

theorem absorbInput : (flatten (TranscriptStep.absorbParts (encodeState JFr_SeedBoundary.numeric)
    160#u8 frame)).map Fin.val=JFp_Query00Absorb.message := by rfl

theorem readInput : (flatten (TranscriptStep.readParts (encodeState absorbed) 1#u8)).map Fin.val=
    JFp_Query00Read.message := by rfl

theorem ratchetInput : (flatten (TranscriptStep.readParts (encodeState absorbed) 2#u8)).map Fin.val=
    JFp_Query00Ratchet.message := by rfl

theorem absorbHash : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
    (TranscriptStep.absorbParts (encodeState JFr_SeedBoundary.numeric) 160#u8 frame)=encodeState absorbed := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [absorbInput,JFp_Query00Absorb.checked]
  rfl

theorem readHash : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
    (TranscriptStep.readParts (encodeState absorbed) 1#u8)=encodeState block := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [readInput,JFp_Query00Read.checked]
  rfl

theorem ratchetHash : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
    (TranscriptStep.readParts (encodeState absorbed) 2#u8)=encodeState ratchet := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [ratchetInput,JFp_Query00Ratchet.checked]
  rfl

/-- Three concrete SHA calls of the first real semantic row, in source order. -/
theorem source {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    r1_wire.SemanticTranscript.sample_block_validated D0
      (⟨encodeState JFr_SeedBoundary.numeric,hash,0#u8⟩ : r1_wire.SemanticTranscript Hash)
      0#u8 JFw_NativeRow00.record=ok (.Ok (encodeState block),
        (⟨encodeState ratchet,hash,1#u8⟩ : r1_wire.SemanticTranscript Hash)) := by
  dsimp only
  rw [realFrame,TranscriptStep.step_of_add _ _ 0#u8 160#u8 1#u8 frame rfl (by rfl) (by rfl)]
  change (do let a ← ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
      (TranscriptStep.absorbParts (encodeState JFr_SeedBoundary.numeric) 160#u8 frame))
             let b ← ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
               (TranscriptStep.readParts a 1#u8))
             let s ← ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
               (TranscriptStep.readParts a 2#u8))
             ok ((core.result.Result.Ok b : core.result.Result (Array U8 32#usize) r1_wire.Error),(⟨s,hash,1#u8⟩ : r1_wire.SemanticTranscript Hash)))=_
  rw [absorbHash,bind_tc_ok,readHash,bind_tc_ok,ratchetHash,bind_tc_ok]

#print axioms realFrame
#print axioms absorbInput
#print axioms readInput
#print axioms ratchetInput
#print axioms absorbHash
#print axioms readHash
#print axioms ratchetHash
#print axioms source
end AspisR1.JFp_Query00Source
