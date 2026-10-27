import FJc_InstalledParts
set_option autoImplicit false
namespace AspisR1.FJc_ArrayRead
open Aeneas Aeneas.Std Result
/-- Pure coordinate adapter preserves the original indexed operand. -/
theorem map {A B : Type} {N : Usize} (f : A → B) (a : Array A N) (i : Usize) (x : A)
    (run : Array.index_usize a i=ok x) :
    Array.index_usize (FIn_WeightsInstall.mapArray f a) i=ok (f x) := by
  unfold Array.index_usize at run ⊢
  split at run
  · cases run
  · rename_i v hv
    cases Result.ok.inj run
    change a.val[i.val]?=some x at hv
    change (match (a.val.map f)[i.val]? with | none => fail Error.arrayOutOfBounds | some y => ok y)=ok (f x)
    simp only [List.getElem?_map,hv,Option.map_some]
#print axioms map
end AspisR1.FJc_ArrayRead
