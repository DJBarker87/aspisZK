import NFG_ArrayWindow
import NFP_QueryCuts
set_option autoImplicit false
namespace AspisR1.NFP_FrameExt
open Aeneas Aeneas.Std Result AspisR1Stage2
/-- Lift one arbitrary observed raw limb to the complete64-row carrier.
The native premise is coordinate coverage, not a whole-output equality. -/
theorem raw (xs ys : alloc.vec.Vec (Array U64 4#usize))
 (hx : xs.val.length=64) (hy : ys.val.length=64)
 (observed : ∀ row : Fin 64, ∀ limb : Fin 4,
  xs.val[row.val]!.val[limb.val]! = ys.val[row.val]!.val[limb.val]!) : xs=ys := by
 apply Subtype.ext
 apply List.ext_getElem
 · omega
 · intro i hi hj
   have bound : i<64 := by omega
   have h := NFG_ArrayWindow.ext xs.val[i]! ys.val[i]! (observed ⟨i,bound⟩)
   simpa only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem hi,
     List.getElem?_eq_getElem hj,Option.getD_some] using h
#print axioms raw
end AspisR1.NFP_FrameExt
