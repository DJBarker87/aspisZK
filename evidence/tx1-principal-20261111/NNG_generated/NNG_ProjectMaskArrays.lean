import NNG_ProjectMaskCells
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ProjectMaskArrays
open Aeneas Aeneas.Std NNG_Emitted NNG_Transport NNG_LIBScalar NNG_LIBArrays
open AspisR1.NMT_Transport (arr)

theorem first (fallback : Value) (claims : Claims) (i : Usize) (hi : i.val < 16) :
    LIB_VScalarCarriers.toRaw (project fallback (NNG_FromFnValues136.firstValue claims i)) =
      LIB_VScalarCarriers.toRaw (LIB_VMask.cell (projectClaims fallback claims) ⟨i.val,by omega⟩) := by
  rw [NNG_FromFnValues136.firstValue,dif_pos hi]
  exact congrArg LIB_VScalarCarriers.toRaw (NNG_ProjectMaskCells.cell fallback claims i (by omega)).symm
#print axioms first

theorem low (fallback : Value) (claims : Claims) :
    arr (fun q => LIB_VScalarCarriers.toRaw (project fallback q)) (NNG_FromFnValues136.low claims) =
      LIB_VField.c1 (projectClaims fallback claims) := by
  apply Subtype.ext
  change ((OraclePortStdBuilder.indices 16#usize).map (NNG_FromFnValues136.firstValue claims)).map
    (fun q => LIB_VScalarCarriers.toRaw (project fallback q)) = _
  apply List.ext_getElem
  · simp only [List.length_map,NNG_FromFnOn136.indices_length,LIB_VField.c1,List.length_finRange]
    rfl
  · intro i hi hj
    have bound : i<16 := by
      have h := hi
      simp only [List.length_map,NNG_FromFnOn136.indices_length] at h
      change i<16 at h
      exact h
    simp only [List.getElem_map,OraclePortStdBuilder.indices,List.getElem_ofFn,LIB_VField.c1,List.getElem_finRange]
    apply first fallback claims
    change i<16
    exact bound
#print axioms low

theorem second (fallback : Value) (claims : Claims) (i : Usize) (hi : i.val < 10) :
    LIB_VScalarCarriers.toRaw (project fallback (NNG_FromFnValues136.secondValue claims i)) =
      LIB_VScalarCarriers.toRaw (LIB_VMask.cell (projectClaims fallback claims) ⟨16+i.val,by omega⟩) := by
  rw [NNG_FromFnValues136.secondValue,dif_pos hi]
  rw [←NNG_ProjectMaskCells.cell fallback claims (NNG_Offset16.shifted i) (NNG_Offset16.bound i hi)]
  congr 2
  apply Fin.ext
  exact NNG_Offset16.value i hi
#print axioms second

theorem high (fallback : Value) (claims : Claims) :
    arr (fun q => LIB_VScalarCarriers.toRaw (project fallback q)) (NNG_FromFnValues136.high claims) =
      LIB_VField.maskOnly (projectClaims fallback claims) := by
  apply Subtype.ext
  change ((OraclePortStdBuilder.indices 10#usize).map (NNG_FromFnValues136.secondValue claims)).map
    (fun q => LIB_VScalarCarriers.toRaw (project fallback q)) = _
  apply List.ext_getElem
  · simp only [List.length_map,NNG_FromFnOn136.indices_length,LIB_VField.maskOnly,List.length_finRange]
    rfl
  · intro i hi hj
    have bound : i<10 := by
      have h := hi
      simp only [List.length_map,NNG_FromFnOn136.indices_length] at h
      change i<10 at h
      exact h
    simp only [List.getElem_map,OraclePortStdBuilder.indices,List.getElem_ofFn,LIB_VField.maskOnly,List.getElem_finRange]
    apply second fallback claims
    change i<10
    exact bound
#print axioms high
end AspisR1.NNG_ProjectMaskArrays
