import NBJ_PaddingBits

set_option autoImplicit false
noncomputable section
namespace AspisR1.NBJ_PaddingPort
open Aeneas Aeneas.Std Result

/-- Construct the actual partition from the original physical bytes before
running the installed predicate/iterator. No independently selected chunks,
accepted scan or final padding equation is a premise. -/
theorem physical_scan (base : Port3_NativeBatchBody.Ops) {X : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (padding : Slice U8) :
    ∃ ce : core.slice.iter.ChunksExact U8,
      core.slice.Slice.chunks_exact padding 8#usize = ok ce ∧
      (Port3_BatchStd.install base).op0 (core.iter.traits.iterator.IteratorChunksExact U8)
        (Port3_NativeBatchBody.verifier.candidate.batch_tree.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU8Bool
          (Port3_BatchStd.install base) D) ce () =
      NBI_Padding.scan
        (Port3_NativeBatchBody.verifier.candidate.batch_tree.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU8Bool
          (Port3_BatchStd.install base) D) ce.remainder ce.chunks := by
  have run : ∃ ce, core.slice.Slice.chunks_exact padding 8#usize = ok ce := by
    unfold core.slice.Slice.chunks_exact
    split
    · exact ⟨_,rfl⟩
    · rename_i impossible
      simp at impossible
  obtain ⟨ce,run⟩ := run
  exact ⟨ce,run,NBJ_Padding.scan_exact base D ce.chunks ce.remainder⟩

#print axioms physical_scan
end AspisR1.NBJ_PaddingPort
end
