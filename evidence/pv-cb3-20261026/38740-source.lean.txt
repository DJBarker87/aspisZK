import R1Z.PV_CB3_StagedUnpack
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_StagedResult
open Aeneas Aeneas.Std Result ProverRwFull

theorem decode_pipeline (rank : Array U32 8#usize) :
    PV_CB3_StagedDecode.decode (PV_CB3_StagedKernel.pipeline rank) =
      ok (PV_CB3_StagedUnpack.raw (PV_CB3_StagedKernel.pipeline rank)) := by
  apply PV_CB3_StagedUnpack.source
  exact PV_CB3_StagedValue.kernel_canonical rank

/-- Complete owned-reference Result, with canonicality derived internally. -/
theorem source (block : Array U8 32#usize) :
    PV_CB3_StagedSource.staged_reference.gamma block =
      (do let rank ← PV_CB3_StagedSource.staged_reference.words block
          ok (PV_CB3_StagedUnpack.raw (PV_CB3_StagedKernel.pipeline rank))) := by
  rw [PV_CB3_StagedKernel.source]
  simp only [decode_pipeline]

theorem value (rank : Array U32 8#usize) :
    PV_CB3_SamplerCarry.value PV_CB3_SamplerWord.base
      (PV_CB3_StagedUnpack.values (PV_CB3_StagedUnpack.raw (PV_CB3_StagedKernel.pipeline rank))) =
    PV_CB3_SamplerCarry.value PV_CB3_SamplerWord.radix (rank.val.map UScalar.val) %
      (PV_CB3_SamplerWord.base ^ 8 - 1) + 1 := by
  rw [PV_CB3_StagedUnpack.raw_values]
  exact PV_CB3_StagedValue.kernel_value rank
#print axioms decode_pipeline
#print axioms source
#print axioms value
end R1Z.PV_CB3_StagedResult
