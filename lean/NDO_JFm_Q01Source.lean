import NDO_JFp_Query00Source
import NDO_JFm_Q01Absorb
import NDO_JFm_Q01Reads
import NDO_JFw_NativeRow01
import RPz7_ExtractedDigest32SamplerTransport
set_option autoImplicit false
namespace AspisR1.JFm_Q01Source
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
def frame : Slice U8 := ⟨[0#u8,0#u8,0#u8,0#u8,0#u8],by scalar_tac⟩
def absorbed : State := JFp_SHADigest.output JFm_Q01Absorb.result
def block : State := JFp_SHADigest.output JFm_Q01Read.result
def ratchet : State := JFp_SHADigest.output JFm_Q01Ratchet.result
def record : r1_wire.ValidatedRecord := ⟨1#u8,JFw_NativeRow01.record⟩
theorem realFrame : JFw_NativeRow01.record=frame := by
  apply Subtype.ext
  rfl
#print axioms realFrame
theorem absorbInput : (flatten (TranscriptStep.absorbParts (encodeState JFp_Query00Source.ratchet) 161#u8 frame)).map Fin.val=JFm_Q01Absorb.message := by rfl
#print axioms absorbInput
theorem absorbHash : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.absorbParts (encodeState JFp_Query00Source.ratchet) 161#u8 frame)=encodeState absorbed := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [absorbInput,JFm_Q01Absorb.checked]
  rfl
#print axioms absorbHash
theorem readInput : (flatten (TranscriptStep.readParts (encodeState absorbed) 1#u8)).map Fin.val=JFm_Q01Read.message := by rfl
#print axioms readInput
theorem readHash : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.readParts (encodeState absorbed) 1#u8)=encodeState block := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [readInput,JFm_Q01Read.checked]
  rfl
#print axioms readHash
theorem ratchetInput : (flatten (TranscriptStep.readParts (encodeState absorbed) 2#u8)).map Fin.val=JFm_Q01Ratchet.message := by rfl
#print axioms ratchetInput
theorem ratchetHash : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.readParts (encodeState absorbed) 2#u8)=encodeState ratchet := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [ratchetInput,JFm_Q01Ratchet.checked]
  rfl
#print axioms ratchetHash
theorem source {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    r1_wire.SemanticTranscript.sample_block_validated D0
      (⟨encodeState JFp_Query00Source.ratchet,hash,1#u8⟩ : r1_wire.SemanticTranscript Hash)
      1#u8 JFw_NativeRow01.record=ok (.Ok (encodeState block),
        (⟨encodeState ratchet,hash,2#u8⟩ : r1_wire.SemanticTranscript Hash)) := by
  dsimp only
  rw [realFrame,TranscriptStep.step_of_add _ _ 1#u8 161#u8 2#u8 frame rfl (by rfl) (by rfl)]
  change (do let a ← ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
      (TranscriptStep.absorbParts (encodeState JFp_Query00Source.ratchet) 161#u8 frame))
             let b ← ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
               (TranscriptStep.readParts a 1#u8))
             let s ← ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
               (TranscriptStep.readParts a 2#u8))
             ok ((core.result.Result.Ok b : core.result.Result (Array U8 32#usize) r1_wire.Error),(⟨s,hash,2#u8⟩ : r1_wire.SemanticTranscript Hash)))=_
  rw [absorbHash,bind_tc_ok,readHash,bind_tc_ok,ratchetHash,bind_tc_ok]
#print axioms source
theorem word00 : AspisV8R19.SamplerWords.word block ⟨0,by omega⟩=2713775439 := by rfl
#print axioms word00
theorem word01 : AspisV8R19.SamplerWords.word block ⟨1,by omega⟩=2224555041 := by rfl
#print axioms word01
theorem word02 : AspisV8R19.SamplerWords.word block ⟨2,by omega⟩=857534472 := by rfl
#print axioms word02
theorem word03 : AspisV8R19.SamplerWords.word block ⟨3,by omega⟩=2424942534 := by rfl
#print axioms word03
theorem word04 : AspisV8R19.SamplerWords.word block ⟨4,by omega⟩=1028589116 := by rfl
#print axioms word04
theorem word05 : AspisV8R19.SamplerWords.word block ⟨5,by omega⟩=824686787 := by rfl
#print axioms word05
theorem word06 : AspisV8R19.SamplerWords.word block ⟨6,by omega⟩=3247162646 := by rfl
#print axioms word06
theorem word07 : AspisV8R19.SamplerWords.word block ⟨7,by omega⟩=163523910 := by rfl
#print axioms word07
theorem rank : SourceSamplerByteRank.rank (encodeState block)=4408595912786711459720234687148435670066939797869725462423444142639110221135 := by
  unfold SourceSamplerByteRank.rank
  rw [state_roundtrip,←SamplerBlockRank.word_numeral_eq_rank]
  change SamplerPass.numeral (2^32) ([AspisV8R19.SamplerWords.word block ⟨0,by omega⟩,AspisV8R19.SamplerWords.word block ⟨1,by omega⟩,AspisV8R19.SamplerWords.word block ⟨2,by omega⟩,AspisV8R19.SamplerWords.word block ⟨3,by omega⟩,AspisV8R19.SamplerWords.word block ⟨4,by omega⟩,AspisV8R19.SamplerWords.word block ⟨5,by omega⟩,AspisV8R19.SamplerWords.word block ⟨6,by omega⟩,AspisV8R19.SamplerWords.word block ⟨7,by omega⟩].reverse)=4408595912786711459720234687148435670066939797869725462423444142639110221135
  rw [word00,word01,word02,word03,word04,word05,word06,word07]
  rfl
#print axioms rank
theorem digits : SamplerNatModel.qm31Digits 4408595912786711459720234687148435670066939797869725462423444142639110221135=[941725965,710616451,1814298802,371706036] := by rfl
#print axioms digits
theorem semantic {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    ∃ q : AspisR1PublicPreparation.aspis_core.field.QM31,
    r1_wire.SemanticTranscript.semantic_validated D0
      (⟨encodeState JFp_Query00Source.ratchet,hash,1#u8⟩ : r1_wire.SemanticTranscript Hash)
      record=ok (.Ok q,(⟨encodeState ratchet,hash,2#u8⟩ : r1_wire.SemanticTranscript Hash)) ∧
    ExtractedQM31SamplerCorrect.coordinates (AspisR1PublicPreparation.SamplerTransport.toOld q)=[941725965,710616451,1814298802,371706036] := by
  obtain ⟨q,call,canon,coords⟩ := AspisR1PublicPreparation.SamplerTransport.sample_total (encodeState block)
  refine ⟨q,?_,by simpa only [rank,digits] using coords⟩
  simp only [r1_wire.SemanticTranscript.semantic_validated,record,r1_wire.ValidatedRecord.impl.row,
    r1_wire.ValidatedRecord.impl.framed,bind_tc_ok]
  rw [if_neg (by change ¬(1:Nat)>24;omega)]
  rw [source,bind_tc_ok]
  change (do let v ← AspisR1PublicPreparation.sampler.qm31_sample (encodeState block)
             ok ((core.result.Result.Ok v : core.result.Result aspis_core.field.QM31 r1_wire.Error),
               (⟨encodeState ratchet,hash,2#u8⟩ : r1_wire.SemanticTranscript Hash)))=_
  rw [call,bind_tc_ok]
#print axioms semantic
end AspisR1.JFm_Q01Source
