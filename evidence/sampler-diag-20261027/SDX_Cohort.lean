import SDX_CohortGeneric
import SDX_PResult
import SDX_ZeroResult
import SDX_P1Result
import SDX_FFResult
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace SDX_Cohort
open AspisR1GammaCaller.DigitsModel AspisR1.SourceSamplerByteRank AspisR1.SamplerNatModel AspisR1.SamplerMachineBounds

def digitsP : Array U32 8#usize := ⟨[0#u32,1#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32],by simp⟩

theorem rankP : rank SDX_PResult.block = 2147483647 := by
  unfold rank
  rw [R0C.ModuloField.blockRank_value]
  norm_num [Fin.sum_univ_succ, AspisV8R19.SqueezeOracleBridge.decodeState,
    AspisV8R19.SqueezeOracleBridge.decodeByte, SDX_PResult.block]
#print axioms rankP

theorem resultP : AspisR1Post25Sampler.sampler.low_base_p_digits SDX_PResult.block = ok (digitsP,0#u32) := by
  apply SDX_CohortGeneric.concrete
  · rw [rankP]
    norm_num [values,digitsP,ordinaryDigits,lowDigits,P]
  · rw [rankP]
    norm_num [P]
#print axioms resultP

def digitsZero : Array U32 8#usize := ⟨[0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32],by simp⟩

theorem rankZero : rank SDX_ZeroResult.block = 0 := by
  unfold rank
  rw [R0C.ModuloField.blockRank_value]
  norm_num [Fin.sum_univ_succ, AspisV8R19.SqueezeOracleBridge.decodeState,
    AspisV8R19.SqueezeOracleBridge.decodeByte, SDX_ZeroResult.block]
#print axioms rankZero

theorem resultZero : AspisR1Post25Sampler.sampler.low_base_p_digits SDX_ZeroResult.block = ok (digitsZero,0#u32) := by
  apply SDX_CohortGeneric.concrete
  · rw [rankZero]
    norm_num [values,digitsZero,ordinaryDigits,lowDigits,P]
  · rw [rankZero]
    norm_num [P]
#print axioms resultZero

def digitsP1 : Array U32 8#usize := ⟨[1#u32,1#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32],by simp⟩

theorem rankP1 : rank SDX_P1Result.block = 2147483648 := by
  unfold rank
  rw [R0C.ModuloField.blockRank_value]
  norm_num [Fin.sum_univ_succ, AspisV8R19.SqueezeOracleBridge.decodeState,
    AspisV8R19.SqueezeOracleBridge.decodeByte, SDX_P1Result.block]
#print axioms rankP1

theorem resultP1 : AspisR1Post25Sampler.sampler.low_base_p_digits SDX_P1Result.block = ok (digitsP1,0#u32) := by
  apply SDX_CohortGeneric.concrete
  · rw [rankP1]
    norm_num [values,digitsP1,ordinaryDigits,lowDigits,P]
  · rw [rankP1]
    norm_num [P]
#print axioms resultP1

def digitsFF : Array U32 8#usize := ⟨[255#u32,2048#u32,7168#u32,14336#u32,17920#u32,14336#u32,7168#u32,2048#u32],by simp⟩

theorem rankFF : rank SDX_FFResult.block = 115792089237316195423570985008687907853269984665640564039457584007913129639935 := by
  unfold rank
  rw [R0C.ModuloField.blockRank_value]
  norm_num [Fin.sum_univ_succ, AspisV8R19.SqueezeOracleBridge.decodeState,
    AspisV8R19.SqueezeOracleBridge.decodeByte, SDX_FFResult.block]
#print axioms rankFF

theorem resultFF : AspisR1Post25Sampler.sampler.low_base_p_digits SDX_FFResult.block = ok (digitsFF,256#u32) := by
  apply SDX_CohortGeneric.concrete
  · rw [rankFF]
    norm_num [values,digitsFF,ordinaryDigits,lowDigits,P]
  · rw [rankFF]
    norm_num [P]
#print axioms resultFF
end SDX_Cohort
