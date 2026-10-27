import R1Z.PV_Src_PortDigestEta
import R1Z.PV_Src_PortNoop
set_option autoImplicit false
namespace R1Z.PV_Src_PortNodeCopy
open Aeneas Aeneas.Std Result BuilderForestStdPort BuilderForestAdmissionPort

def joined (left right : Array U32 8#usize) : Array U32 16#usize :=
  ⟨left.val ++ right.val,by simp only [List.length_append,left.property,right.property];decide⟩

def run (left right : Array U32 8#usize) : Result (Array U32 16#usize) := do
  let state := Array.repeat 16#usize aspis_core.field.M31.ZERO
  let (s,back) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice
    (core.slice.index.SliceIndexRangeToUsizeSlice aspis_core.field.M31))
    state {«end» := poseidon2.DIGEST_ELEMS}
  let l ← lift (Array.to_slice left)
  let l1 ← core.slice.Slice.copy_from_slice aspis_core.field.M31.Insts.CoreMarkerCopy s l
  let state1 := back l1
  let (s1,back1) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice
    (core.slice.index.SliceIndexRangeFromUsizeSlice aspis_core.field.M31))
    state1 {start := poseidon2.DIGEST_ELEMS}
  let r ← lift (Array.to_slice right)
  let r1 ← core.slice.Slice.copy_from_slice aspis_core.field.M31.Insts.CoreMarkerCopy s1 r
  ok (back1 r1)

theorem source (left right : Array U32 8#usize) : run left right = ok (joined left right) := by
  rw [PV_Src_PortDigestEta.source left,PV_Src_PortDigestEta.source right]
  simp only [run,joined,poseidon2.DIGEST_ELEMS,aspis_core.field.M31.ZERO]
  rfl

#print axioms source
end R1Z.PV_Src_PortNodeCopy
