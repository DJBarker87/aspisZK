import NNG_LIBMaskHigh
import NNG_LIBField
import NNG_LIBArrayDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ProjectMaskCells
open Aeneas Aeneas.Std NNG_Emitted NNG_Transport NNG_LIBScalar NNG_LIBArrays NNG_LIBArrayDomain
open AspisR1.NMT_Transport (arr)

theorem cell (fallback : Value) (claims : Claims) (i : Usize) (hi : i.val < 29) :
    LIB_VMask.cell (projectClaims fallback claims) ⟨i.val,hi⟩ =
      project fallback (NNG_Array136.cell claims i hi) := by
  unfold LIB_VMask.cell projectClaims projectArray arr NNG_Array136.cell NNG_Array136.row0 NNG_Array136.get
  simp only [List.getElem_map]
  rfl
#print axioms cell

theorem raw_array {n : Usize} (fallback : Value) (a : Array Q n) (domain : DomainArray a) :
    arr toT1 a = LIB_VScalarCarriers.array LIB_VScalarCarriers.toRaw (projectArray fallback a) := by
  apply Subtype.ext
  change a.val.map toT1 = (a.val.map (project fallback)).map LIB_VScalarCarriers.toRaw
  rw [List.map_map]
  apply List.map_congr_left
  intro q member
  exact (NNG_LIBField.raw_project fallback q (domain q member)).symm
#print axioms raw_array
end AspisR1.NNG_ProjectMaskCells
