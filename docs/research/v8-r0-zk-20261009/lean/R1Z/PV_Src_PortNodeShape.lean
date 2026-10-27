import R1Z.PV_Src_PortBindPair
set_option autoImplicit false
namespace R1Z.PV_Src_PortNodeShape
open Aeneas Aeneas.Std Result BuilderForestStdPort BuilderForestAdmissionPort

def finish (s : Array U32 16#usize) : Result (Array U32 8#usize) := do
  let i ← lift (Usize.wrapping_sub poseidon2.POSEIDON2_WIDTH 1#usize)
  let m ← Array.index_usize s i
  let m1 ← aspis_core.field.M31.add m poseidon2.MERKLE_NODE_COMPRESSION_V3_TWEAK
  let i1 ← lift (Usize.wrapping_sub poseidon2.POSEIDON2_WIDTH 1#usize)
  let s1 ← Array.update s i1 m1
  let s2 ← poseidon2.permute_optimized_with_trace
    (sourceExternalLinear := PV_Src_ExternalReference.dictionary) PV_Src_PortNoop.callback s1 ()
  core.array.from_fn 8#usize
    poseidon2.merkle_node_compress_v3.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeM31 s2

theorem source (left right : Array U32 8#usize) :
    poseidon2.merkle_node_compress_v3
      (sourceExternalLinear := PV_Src_ExternalReference.dictionary) left right =
    finish (PV_Src_PortNodeCopy.joined left right) := by
  rw [PV_Src_PortDigestEta.source left,PV_Src_PortDigestEta.source right]
  simp only [poseidon2.merkle_node_compress_v3,finish,PV_Src_PortNodeCopy.joined,
    poseidon2.DIGEST_ELEMS,aspis_core.field.M31.ZERO]
  rfl

#print axioms source
end R1Z.PV_Src_PortNodeShape
