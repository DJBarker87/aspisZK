import NDD_PackModel
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDD_PackComposition
open FIq_Native NDD_PackModel

def paddingCut (values : Slice field.QM31) :
    Result (field.QM31 × field.QM31 × field.QM31 × field.QM31) := do
  let i := Slice.len values
  massert (i <= 4#usize)
  let padded := Array.repeat 4#usize field.QM31.ZERO
  let i1 := Slice.len values
  let (s, index_mut_back) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice field.QM31)) padded
      { «end» := i1 }
  let s1 ←
    core.slice.Slice.copy_from_slice field.QM31.Insts.CoreMarkerCopy s values
  let padded1 := index_mut_back s1
  let v0 ← Array.index_usize padded1 0#usize
  let v1 ← Array.index_usize padded1 1#usize
  let v2 ← Array.index_usize padded1 2#usize
  let v3 ← Array.index_usize padded1 3#usize
  ok (v0,v1,v2,v3)

/-- Exact cohort prefix and SAME padded values feed the extracted arithmetic
reference. Native prefix/value transport remains a separate P6 obligation. -/
theorem source_reference (values : Slice field.QM31) :
    (do let q ← field.qm31_pack_base4 values;ok (words q)) = (do
      let (v0,v1,v2,v3) ← paddingCut values
      NDD_Reference.pack_ref
        (Array.make 4#usize [words v0,words v1,words v2,words v3])) := by
  rw [source_cut]
  cases hm : core.array.Array.index_mut
    (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice field.QM31))
    (Array.repeat 4#usize field.QM31.ZERO) { «end» := Slice.len values } with
  | ok pair =>
    rcases pair with ⟨s,back⟩
    simp [paddingCut,hm,bind_assoc_eq,← reference_tail]
  | fail e => simp [paddingCut,hm]
  | div => simp [paddingCut,hm]

#print axioms source_reference
end NDD_PackComposition
