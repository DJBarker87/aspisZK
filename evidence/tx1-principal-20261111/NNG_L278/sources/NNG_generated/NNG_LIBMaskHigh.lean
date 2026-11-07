import NNG_LIBMaskLow
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_LIBMaskHigh
open Aeneas Aeneas.Std NNG_Emitted NNG_Transport
open NNG_LIBScalar NNG_LIBArrays
open AspisR1.NMT_Transport (arr)

theorem second_value (claims : LIB_VCarriers.Claims) (i : Usize) (hi : i.val < 10) :
    toT1 (NNG_FromFnValues136.secondValue (lowerClaims claims) i) =
      LIB_VScalarCarriers.toRaw (LIB_VMask.cell claims ⟨16+i.val,by omega⟩) := by
  rw [NNG_FromFnValues136.secondValue,dif_pos hi,NNG_LIBMaskCells.cell]
  congr 2
  apply Fin.ext
  exact NNG_Offset16.value i hi
#print axioms second_value

theorem high (claims : LIB_VCarriers.Claims) :
    arr toT1 (NNG_FromFnValues136.high (lowerClaims claims)) = LIB_VField.maskOnly claims := by
  apply Subtype.ext
  change ((OraclePortStdBuilder.indices 10#usize).map (NNG_FromFnValues136.secondValue (lowerClaims claims))).map toT1 =
    (List.finRange 10).map (fun j => LIB_VScalarCarriers.toRaw (LIB_VMask.cell claims ⟨16+j.val,by omega⟩))
  apply List.ext_getElem
  · simp only [List.length_map,NNG_FromFnOn136.indices_length,List.length_finRange]
    rfl
  · intro i hi hj
    have bound : i < 10 := by
      have h := hi
      simp only [List.length_map,NNG_FromFnOn136.indices_length] at h
      change i < 10 at h
      exact h
    simp only [List.getElem_map,OraclePortStdBuilder.indices,List.getElem_ofFn,List.getElem_finRange]
    apply second_value claims
    change i < 10
    exact bound
#print axioms high
end AspisR1.NNG_LIBMaskHigh
