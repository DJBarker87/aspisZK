import JFp_Query00Source
import ExtractedDigest32SamplerTransport
set_option autoImplicit false
namespace AspisR1.JFp_Query00Sample
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
def value : aspis_core.field.QM31 := ⟨⟨399501241#u32,284689285#u32⟩,⟨1852519329#u32,449773828#u32⟩⟩
theorem source : sampler.qm31_sample (encodeState JFp_Query00Source.block)=ok value := by
  obtain ⟨q,call,canon,coords⟩ := SamplerTransport.sample_total (encodeState JFp_Query00Source.block)
  rw [rank,digits] at coords
  change [q.c0.a.val,q.c0.b.val,q.c1.a.val,q.c1.b.val]=[399501241,284689285,1852519329,449773828] at coords
  have e0 : q.c0.a=399501241#u32 := UScalar.eq_of_val_eq (List.cons.inj coords).1
  have e1 : q.c0.b=284689285#u32 := UScalar.eq_of_val_eq (List.cons.inj (List.cons.inj coords).2).1
  have e2 : q.c1.a=1852519329#u32 := UScalar.eq_of_val_eq (List.cons.inj (List.cons.inj (List.cons.inj coords).2).2).1
  have e3 : q.c1.b=449773828#u32 := UScalar.eq_of_val_eq (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj coords).2).2).2).1
  have same : q=value := by
    rcases q with ⟨⟨a,b⟩,⟨c,d⟩⟩
    dsimp only at e0 e1 e2 e3
    cases e0;cases e1;cases e2;cases e3
    rfl
  exact same ▸ call
#print axioms source
end AspisR1.JFp_Query00Sample
