import NNG_Calls345
import NMT_R2_ListEquality
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Compare345
open Aeneas Aeneas.Std NMT_345

theorem equal {N : Usize} (xs : Slice U8) (ys : Array U8 N) :
 NNG_Calls345.eqArray core.cmp.PartialEqU8 xs ys=.ok (decide (xs.val=ys.val)) :=
 NMT_R2_ListEquality.source xs.val ys.val
#print axioms equal

theorem unequal {N : Usize} (xs : Slice U8) (ys : Array U8 N) :
 NNG_Calls345.neArray core.cmp.PartialEqU8 xs ys=.ok (!decide (xs.val=ys.val)) := by
 unfold NNG_Calls345.neArray
 rw [equal]
 rfl
#print axioms unequal

theorem projected (xs ys : List U8) :
 (xs.map byte=ys.map byte) ↔ xs=ys :=
 ⟨List.map_injective_iff.mpr byte_injective,fun h=>congrArg (List.map byte) h⟩
#print axioms projected
end AspisR1.NNG_Compare345
