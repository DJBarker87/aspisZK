import NNG_LIBMaskCells
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_LIBMaskLow
open Aeneas Aeneas.Std NNG_Emitted NNG_Transport
open NNG_LIBScalar NNG_LIBArrays
open AspisR1.NMT_Transport (arr)

theorem first_value (claims : LIB_VCarriers.Claims) (i : Usize) (hi : i.val < 16) :
    toT1 (NNG_FromFnValues136.firstValue (lowerClaims claims) i) =
      LIB_VScalarCarriers.toRaw (LIB_VMask.cell claims ⟨i.val,by omega⟩) := by
  rw [NNG_FromFnValues136.firstValue,dif_pos hi]
  exact NNG_LIBMaskCells.cell claims i (by omega)
#print axioms first_value

theorem low (claims : LIB_VCarriers.Claims) :
    arr toT1 (NNG_FromFnValues136.low (lowerClaims claims)) = LIB_VField.c1 claims := by
  apply Subtype.ext
  change ((OraclePortStdBuilder.indices 16#usize).map (NNG_FromFnValues136.firstValue (lowerClaims claims))).map toT1 =
    (List.finRange 16).map (fun j => LIB_VScalarCarriers.toRaw (LIB_VMask.cell claims ⟨j.val,by omega⟩))
  apply List.ext_getElem
  · simp only [List.length_map,NNG_FromFnOn136.indices_length,List.length_finRange]
    rfl
  · intro i hi hj
    have bound : i < 16 := by simpa only [List.length_map,NNG_FromFnOn136.indices_length] using hi
    simp only [List.getElem_map,OraclePortStdBuilder.indices,List.getElem_ofFn,List.getElem_finRange]
    exact first_value claims _ bound
#print axioms low
end AspisR1.NNG_LIBMaskLow
