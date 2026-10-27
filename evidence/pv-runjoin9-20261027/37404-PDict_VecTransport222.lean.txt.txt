import R1Z.PDict_Static222_15
set_option autoImplicit false
namespace R1Z.PDict_VecTransport222
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterDictionaryMap

theorem index_map {A B : Type} (f : A → B) (v : alloc.vec.Vec A) (i : Usize) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice B) (vecMap f v) i =
      resultMap f (alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice A) v i) := by
  simp only [alloc.vec.Vec.index, core.slice.index.SliceIndexUsizeSlice,
    core.slice.index.Usize.index, Slice.index_usize]
  cases h : v.val[i.val]? <;> simp [vecMap, resultMap, h]
#print axioms index_map
end R1Z.PDict_VecTransport222
