import Port4B_ByteWord

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4B_PaddingWord
open Aeneas Aeneas.Std Result AspisR1Stage2

/-- The actual native predicate returning false proves that ALL eight
original bytes in this reached chunk are zero. -/
theorem zero_bytes (base : Port3_NativeBatchBody.Ops) {X : Type}
    (D : aspis_core.digest.Digest32 X) (chunk : Slice U8)
    (returned : Port3_NativeBatchBody.verifier.candidate.batch_tree.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU8Bool.call_mut
      (Port3_BatchStd.install base) D () chunk=ok (false,())) :
    ∀ b∈chunk.val, b=0#u8 := by
  unfold Port3_NativeBatchBody.verifier.candidate.batch_tree.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU8Bool.call_mut at returned
  obtain ⟨r,read,fields⟩ := WP.spec_imp_exists
    (core.array.TryFromArrayCopySlice.try_from.step 8#usize core.marker.CopyU8 chunk)
  rw [read,bind_tc_ok] at returned
  cases r with
  | Err e => cases returned
  | Ok word =>
    simp only [Port3_BatchStd.install,Port3_BatchStd.unwrap8,lift,bind_tc_ok] at returned
    have bits := congrArg Prod.fst (Result.ok.inj returned)
    have zero : core.num.U64.from_le_bytes word=0#u64 := by simpa using bits
    intro b mem
    exact Port4B_ByteWord.u64_zero word zero b (by rw [fields.1];exact mem)

#print axioms zero_bytes
end AspisR1.Port4B_PaddingWord
end
