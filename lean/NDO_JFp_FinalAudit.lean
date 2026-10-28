import RPz8_Rc10_Top
import NDO_JFp_SeededFixture
import NDO_JFp_Query00Source
import RPz7_ExtractedDigest32SamplerTransport
set_option autoImplicit false
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
namespace AspisR1.JFp_Query00Rank
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisV8R19.SqueezeOracleBridge
theorem word00 : AspisV8R19.SamplerWords.word JFp_Query00Source.block ⟨0,by omega⟩=4228484025 := by rfl
#print axioms word00
theorem word01 : AspisV8R19.SamplerWords.word JFp_Query00Source.block ⟨1,by omega⟩=3811825162 := by rfl
#print axioms word01
theorem word02 : AspisV8R19.SamplerWords.word JFp_Query00Source.block ⟨2,by omega⟩=3397035723 := by rfl
#print axioms word02
theorem word03 : AspisV8R19.SamplerWords.word JFp_Query00Source.block ⟨3,by omega⟩=3614355551 := by rfl
#print axioms word03
theorem word04 : AspisV8R19.SamplerWords.word JFp_Query00Source.block ⟨4,by omega⟩=614227251 := by rfl
#print axioms word04
theorem word05 : AspisV8R19.SamplerWords.word JFp_Query00Source.block ⟨5,by omega⟩=4132734922 := by rfl
#print axioms word05
theorem word06 : AspisV8R19.SamplerWords.word JFp_Query00Source.block ⟨6,by omega⟩=493133792 := by rfl
#print axioms word06
theorem word07 : AspisV8R19.SamplerWords.word JFp_Query00Source.block ⟨7,by omega⟩=1845821337 := by rfl
#print axioms word07
theorem rank : SourceSamplerByteRank.rank (encodeState JFp_Query00Source.block)=49763244805704138913778688584452157401775071847162745985820536971161386978233 := by
  unfold SourceSamplerByteRank.rank
  rw [state_roundtrip,←SamplerBlockRank.word_numeral_eq_rank]
  change SamplerPass.numeral (2^32) ([AspisV8R19.SamplerWords.word JFp_Query00Source.block ⟨0,by omega⟩,AspisV8R19.SamplerWords.word JFp_Query00Source.block ⟨1,by omega⟩,AspisV8R19.SamplerWords.word JFp_Query00Source.block ⟨2,by omega⟩,AspisV8R19.SamplerWords.word JFp_Query00Source.block ⟨3,by omega⟩,AspisV8R19.SamplerWords.word JFp_Query00Source.block ⟨4,by omega⟩,AspisV8R19.SamplerWords.word JFp_Query00Source.block ⟨5,by omega⟩,AspisV8R19.SamplerWords.word JFp_Query00Source.block ⟨6,by omega⟩,AspisV8R19.SamplerWords.word JFp_Query00Source.block ⟨7,by omega⟩].reverse)=49763244805704138913778688584452157401775071847162745985820536971161386978233
  rw [word00,word01,word02,word03,word04,word05,word06,word07]
  rfl
#print axioms rank
theorem digits : SamplerNatModel.qm31Digits 49763244805704138913778688584452157401775071847162745985820536971161386978233=[399501241,284689285,1852519329,449773828] := by rfl
#print axioms digits
theorem sampled : ∃ q : AspisR1PublicPreparation.aspis_core.field.QM31,
    AspisR1PublicPreparation.sampler.qm31_sample (encodeState JFp_Query00Source.block)=ok q ∧
      ExtractedQM31SamplerCorrect.coordinates (AspisR1PublicPreparation.SamplerTransport.toOld q)=
        [399501241,284689285,1852519329,449773828] := by
  obtain ⟨q,call,canon,coords⟩ := AspisR1PublicPreparation.SamplerTransport.sample_total
    (encodeState JFp_Query00Source.block)
  exact ⟨q,call,by simpa only [rank,digits] using coords⟩
#print axioms sampled
end AspisR1.JFp_Query00Rank

#print AspisR1.Rc10_Top.deployed
#print axioms AspisR1.Rc10_Top.deployed
#print AspisR1.JFp_SeededFixture.inhabited
#print axioms AspisR1.JFp_SeededFixture.inhabited
#print axioms AspisR1.JFp_SeedHash.checked
#print axioms AspisR1.JFp_InitBytes.native
#print axioms AspisR1.JFp_SHADigest.seed
#print axioms AspisR1.JFp_SHADigest.source
#print axioms AspisR1.JFp_PrefixRoot.source
#print axioms AspisR1.JFp_SourceSeed.source
#print axioms AspisR1.JFp_InitialValue.source
#print axioms AspisR1.JFp_Query00Source.source
#print axioms AspisR1.JFp_Query00Rank.sampled
