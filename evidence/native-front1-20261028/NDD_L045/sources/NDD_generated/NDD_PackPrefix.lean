import NDD_PackModel
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDD_PackPrefix
open FIq_Native NDD_PackModel

def prefixWith {α : Type} (values : Slice field.QM31)
    (k : field.QM31 → field.QM31 → field.QM31 → field.QM31 → Result α) : Result α := do
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
  k v0 v1 v2 v3

theorem bind_prefix {α β : Type} (values : Slice field.QM31)
    (k : field.QM31 → field.QM31 → field.QM31 → field.QM31 → Result α)
    (g : α → Result β) :
    (do let a ← prefixWith values k;g a) =
      prefixWith values (fun a b c d => do let x ← k a b c d;g x) := by
  simp only [prefixWith,bind_assoc_eq]
  congr 1
  funext ignored
  congr 1
  funext pair
  rcases pair with ⟨s,back⟩
  dsimp only
  simp only [bind_assoc_eq]

theorem source_prefix (values : Slice field.QM31) :
    field.qm31_pack_base4 values = prefixWith values tail := by
  rfl
#print axioms bind_prefix
#print axioms source_prefix
end NDD_PackPrefix
