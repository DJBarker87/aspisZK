import NDO_JGj_LocalPackedTotal
import RPv_FJb_BuilderSelected
import ExtractedMaskReducerOps
set_option autoImplicit false
namespace AspisR1.JGj_RawBounds
open Aeneas Aeneas.Std Result
abbrev Raw := Array U64 4#usize
abbrev Words := Array U32 4#usize
abbrev P := AspisV8R17.RawReducer.P
def Bound (a : Raw) (b : Nat) : Prop := ∀ j : Fin (4#usize).val,(FJb_TailCell.cell a j).val<b
def Canonical (a : Words) : Prop := ∀ j : Fin (4#usize).val,(FJb_TailCell.cell a j).val<P
theorem update (a : Raw) (b : Nat) (i : Usize) (v : U64)
    (hi : i.val<(4#usize).val) (ha : Bound a b) (hv : v.val<b) :
    Bound (a.set i v) b := by
  intro j
  change ((a.val.set i.val v)[j.val]'_).val<b
  rw [List.getElem_set]
  split
  · exact hv
  · exact ha j
#print axioms update
end AspisR1.JGj_RawBounds
