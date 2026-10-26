import JFm_Q14Source
import JFw_NativeRow15
import ExtractedDigest32SamplerTransport
import JFm_Q15Hashes
set_option autoImplicit false
namespace AspisR1.JFm_Q15Source
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
abbrev frame : Slice U8 := JFw_NativeRow15.record
def absorbed : State := JFp_SHADigest.output JFm_Q15Absorb.result
def block : State := JFp_SHADigest.output JFm_Q15Read.result
def ratchet : State := JFp_SHADigest.output JFm_Q15Ratchet.result
def record : r1_wire.ValidatedRecord := ⟨15#u8,JFw_NativeRow15.record⟩
theorem realFrame : JFw_NativeRow15.record=frame := by
  apply Subtype.ext
  rfl
#print axioms realFrame
theorem absorbInput : (flatten (TranscriptStep.absorbParts (encodeState JFm_Q14Source.ratchet) 175#u8 frame)).map Fin.val=JFm_Q15Absorb.message := by rfl
#print axioms absorbInput
theorem absorbHash : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.absorbParts (encodeState JFm_Q14Source.ratchet) 175#u8 frame)=encodeState absorbed := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [absorbInput,JFm_Q15Absorb.checked]
  rfl
#print axioms absorbHash
theorem readInput : (flatten (TranscriptStep.readParts (encodeState absorbed) 1#u8)).map Fin.val=JFm_Q15Read.message := by rfl
#print axioms readInput
theorem readHash : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.readParts (encodeState absorbed) 1#u8)=encodeState block := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [readInput,JFm_Q15Read.checked]
  rfl
#print axioms readHash
theorem ratchetInput : (flatten (TranscriptStep.readParts (encodeState absorbed) 2#u8)).map Fin.val=JFm_Q15Ratchet.message := by rfl
#print axioms ratchetInput
theorem ratchetHash : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.readParts (encodeState absorbed) 2#u8)=encodeState ratchet := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [ratchetInput,JFm_Q15Ratchet.checked]
  rfl
#print axioms ratchetHash
theorem source {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    r1_wire.SemanticTranscript.sample_block_validated D0
      (⟨encodeState JFm_Q14Source.ratchet,hash,15#u8⟩ : r1_wire.SemanticTranscript Hash)
      15#u8 JFw_NativeRow15.record=ok (.Ok (encodeState block),
        (⟨encodeState ratchet,hash,16#u8⟩ : r1_wire.SemanticTranscript Hash)) := by
  dsimp only
  rw [realFrame,TranscriptStep.step_of_add _ _ 15#u8 175#u8 16#u8 frame rfl (by rfl) (by rfl)]
  change (do let a ← ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
      (TranscriptStep.absorbParts (encodeState JFm_Q14Source.ratchet) 175#u8 frame))
             let b ← ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
               (TranscriptStep.readParts a 1#u8))
             let s ← ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
               (TranscriptStep.readParts a 2#u8))
             ok ((core.result.Result.Ok b : core.result.Result (Array U8 32#usize) r1_wire.Error),(⟨s,hash,16#u8⟩ : r1_wire.SemanticTranscript Hash)))=_
  rw [absorbHash,bind_tc_ok,readHash,bind_tc_ok,ratchetHash,bind_tc_ok]
#print axioms source
theorem word00 : AspisV8R19.SamplerWords.word block ⟨0,by omega⟩=156665283 := by rfl
#print axioms word00
theorem word01 : AspisV8R19.SamplerWords.word block ⟨1,by omega⟩=3043570950 := by rfl
#print axioms word01
theorem word02 : AspisV8R19.SamplerWords.word block ⟨2,by omega⟩=1083557867 := by rfl
#print axioms word02
theorem word03 : AspisV8R19.SamplerWords.word block ⟨3,by omega⟩=2368627987 := by rfl
#print axioms word03
theorem word04 : AspisV8R19.SamplerWords.word block ⟨4,by omega⟩=4173604451 := by rfl
#print axioms word04
theorem word05 : AspisV8R19.SamplerWords.word block ⟨5,by omega⟩=831839808 := by rfl
#print axioms word05
theorem word06 : AspisV8R19.SamplerWords.word block ⟨6,by omega⟩=919693547 := by rfl
#print axioms word06
theorem word07 : AspisV8R19.SamplerWords.word block ⟨7,by omega⟩=4272799259 := by rfl
#print axioms word07
theorem rank : SourceSamplerByteRank.rank (encodeState block)=115194440147853783317142501306617332878256303242782219222485803510414257325507 := by
  unfold SourceSamplerByteRank.rank
  rw [state_roundtrip,←SamplerBlockRank.word_numeral_eq_rank]
  change SamplerPass.numeral (2^32) ([AspisV8R19.SamplerWords.word block ⟨0,by omega⟩,AspisV8R19.SamplerWords.word block ⟨1,by omega⟩,AspisV8R19.SamplerWords.word block ⟨2,by omega⟩,AspisV8R19.SamplerWords.word block ⟨3,by omega⟩,AspisV8R19.SamplerWords.word block ⟨4,by omega⟩,AspisV8R19.SamplerWords.word block ⟨5,by omega⟩,AspisV8R19.SamplerWords.word block ⟨6,by omega⟩,AspisV8R19.SamplerWords.word block ⟨7,by omega⟩].reverse)=115194440147853783317142501306617332878256303242782219222485803510414257325507
  rw [word00,word01,word02,word03,word04,word05,word06,word07]
  rfl
#print axioms rank
theorem digits : SamplerNatModel.qm31Digits 115194440147853783317142501306617332878256303242782219222485803510414257325507=[705343446,1948609717,871005084,203308705] := by rfl
#print axioms digits
theorem semantic {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    ∃ q : AspisR1PublicPreparation.aspis_core.field.QM31,
    r1_wire.SemanticTranscript.semantic_validated D0
      (⟨encodeState JFm_Q14Source.ratchet,hash,15#u8⟩ : r1_wire.SemanticTranscript Hash)
      record=ok (.Ok q,(⟨encodeState ratchet,hash,16#u8⟩ : r1_wire.SemanticTranscript Hash)) ∧
    ExtractedQM31SamplerCorrect.coordinates (AspisR1PublicPreparation.SamplerTransport.toOld q)=[705343446,1948609717,871005084,203308705] := by
  obtain ⟨q,call,canon,coords⟩ := AspisR1PublicPreparation.SamplerTransport.sample_total (encodeState block)
  refine ⟨q,?_,by simpa only [rank,digits] using coords⟩
  simp only [r1_wire.SemanticTranscript.semantic_validated,record,r1_wire.ValidatedRecord.impl.row,
    r1_wire.ValidatedRecord.impl.framed,bind_tc_ok]
  rw [if_neg (by change ¬(15:Nat)>24;omega)]
  rw [source,bind_tc_ok]
  change (do let v ← AspisR1PublicPreparation.sampler.qm31_sample (encodeState block)
             ok ((core.result.Result.Ok v : core.result.Result aspis_core.field.QM31 r1_wire.Error),
               (⟨encodeState ratchet,hash,16#u8⟩ : r1_wire.SemanticTranscript Hash)))=_
  rw [call,bind_tc_ok]
#print axioms semantic
end AspisR1.JFm_Q15Source
