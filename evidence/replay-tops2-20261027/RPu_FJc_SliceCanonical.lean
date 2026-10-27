import RPt_FIo_ArrayCanon
set_option autoImplicit false
namespace AspisR1.FJc_SliceCanonical
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE)

theorem read (s : Slice NE) (i : Usize) (x : NE)
    (hs : ∀ y∈s.val,FIo_WideValues.Canon y) (run : Slice.index_usize s i=ok x) :
    FIo_WideValues.Canon x := by
  unfold Slice.index_usize at run
  split at run
  · cases run
  · rename_i y hy
    cases Result.ok.inj run
    change s.val[i.val]?=some x at hy
    exact hs x (List.mem_of_getElem? hy)
#print axioms read
end AspisR1.FJc_SliceCanonical
