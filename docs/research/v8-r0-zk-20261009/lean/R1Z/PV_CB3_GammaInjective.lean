import R1Z.PV_CB3_GammaArrayInjective
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_GammaInjective
open Aeneas Aeneas.Std Result ProverRwFull
open PV_CB3_StagedGammaRank

theorem collision (a b : Array U8 32#usize) :
    result a = result b ↔
      byteRank a % (PV_CB3_SamplerWord.base^8-1) =
      byteRank b % (PV_CB3_SamplerWord.base^8-1) := by
  constructor
  · intro h
    have hv := congrArg outputRank h
    rw [rank,rank] at hv
    omega
  · intro h
    have hv : outputRank (result a) = outputRank (result b) := by
      rw [rank,rank,h]
    have hv' : PV_CB3_SamplerCarry.value PV_CB3_SamplerWord.base
        ((PV_CB3_StagedKernel.pipeline (PV_CB3_StagedWords.words a)).val.map UScalar.val) =
      PV_CB3_SamplerCarry.value PV_CB3_SamplerWord.base
        ((PV_CB3_StagedKernel.pipeline (PV_CB3_StagedWords.words b)).val.map UScalar.val) := by
      simpa only [outputRank,result,PV_CB3_StagedUnpack.raw_values] using hv
    exact congrArg PV_CB3_StagedUnpack.raw (kernel_value_injective _ _ hv')
#print axioms collision
end R1Z.PV_CB3_GammaInjective
