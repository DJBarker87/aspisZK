import NNG_LIBArrays
import LIB_VField
import NNG_FromFnValues136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_LIBMaskCells
open Aeneas Aeneas.Std NNG_Emitted NNG_Transport NNG_Array136
open NNG_LIBScalar NNG_LIBArrays
open AspisR1.NMT_Transport (arr)

theorem cell (claims : LIB_VCarriers.Claims) (i : Usize) (hi : i.val < 29) :
    toT1 (NNG_Array136.cell (lowerClaims claims) i hi) =
      LIB_VScalarCarriers.toRaw (LIB_VMask.cell claims ⟨i.val,hi⟩) := by
  unfold NNG_Array136.cell row0 get lowerClaims lowerArray arr
  simp only [List.getElem_map]
  unfold lower
  rw [fromT1_inverse]
  rfl
#print axioms cell

theorem blind (claims : LIB_VCarriers.Claims) :
    toT1 (NNG_Array136.cell (lowerClaims claims) 27#usize (by decide)) = LIB_VField.g claims :=
  cell claims 27#usize (by decide)
#print axioms blind

theorem alpha (a : LIB_VCarriers.Alpha) : arr toT1 (lowerArray a) = LIB_VCarriers.alphaRaw a := by
  apply Subtype.ext
  simp only [arr,lowerArray,LIB_VCarriers.alphaRaw,LIB_VScalarCarriers.array,List.map_map,Function.comp_def,lower,fromT1_inverse]
#print axioms alpha
end AspisR1.NNG_LIBMaskCells
