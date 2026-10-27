import R1Z.PV_Src_PortNodeCopy
set_option autoImplicit false
namespace R1Z.PV_Src_PortNodeDigest
open Aeneas Aeneas.Std Result R0Z.WriterRefine BuilderForestStdPort BuilderForestAdmissionPort

theorem source (s : Array U32 16#usize) :
    core.array.from_fn 8#usize
      poseidon2.merkle_node_compress_v3.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeM31 s =
    ok (digest8 s) := by
  have hf : ∀ i : Usize, i.val < 8 →
    poseidon2.merkle_node_compress_v3.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut s i =
      ok (s.val[i.val]!,s) := by
    intro i hi
    rw [poseidon2.merkle_node_compress_v3.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut,
      index_ok s i (by simp only [UScalar.ofNatCore_val_eq];omega)]
    rfl
  rw [PV_Src_Forest_DigestArguments.from_fn_nat 8#usize poseidon2.merkle_node_compress_v3.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeM31 s (fun i => s.val[i]!) hf]
  rfl

#print axioms source
end R1Z.PV_Src_PortNodeDigest
