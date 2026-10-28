import R1Z.PV_RDB2C_PV_B2_C_ConstructorRow3
set_option autoImplicit false
noncomputable section
namespace PV_B2_C_ConstructorRows
open Aeneas Aeneas.Std Result PV_B2_C_ArrayTotal PV_B2_C_WeightsNative

/-- Exact fixed factor row 4; all array restorations are retained. -/
def row4 (factors : Factors) (z : Array Point 2#usize) : Result Factors := do
  let scp1 ← Array.index_usize z 1#usize
  let q97 ← aspis_core.field.QM31.mul scp1.x scp1.y
  let (a60, index_mut_back20) ← Array.index_mut_usize factors 4#usize
  let a61 ←
    Array.update a60 0#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, scp1.y, scp1.x, q97 ] :
      Array aspis_core.field.QM31 4#usize)
  let x4 ← host_weights.double scp1.x
  let y4 ← host_weights.double x4
  let q98 ← aspis_core.field.QM31.mul x4 y4
  let factors21 := index_mut_back20 a61
  let (a62, index_mut_back21) ← Array.index_mut_usize factors21 4#usize
  let a63 ←
    Array.update a62 1#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, x4, y4, q98 ] : Array
      aspis_core.field.QM31 4#usize)
  let x5 ← host_weights.double y4
  let y5 ← host_weights.double x5
  let q99 ← aspis_core.field.QM31.mul x5 y5
  let factors22 := index_mut_back21 a63
  let (a64, index_mut_back22) ← Array.index_mut_usize factors22 4#usize
  let a65 ←
    Array.update a64 2#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, x5, y5, q99 ] : Array
      aspis_core.field.QM31 4#usize)
  let x6 ← host_weights.double y5
  let y6 ← host_weights.double x6
  let q100 ← aspis_core.field.QM31.mul x6 y6
  let factors23 := index_mut_back22 a65
  let (a66, index_mut_back23) ← Array.index_mut_usize factors23 4#usize
  let a67 ←
    Array.update a66 3#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, x6, y6, q100 ] : Array
      aspis_core.field.QM31 4#usize)
  let x7 ← host_weights.double y6
  let y7 ← host_weights.double x7
  let q101 ← aspis_core.field.QM31.mul x7 y7
  let factors24 := index_mut_back23 a67
  let (a68, index_mut_back24) ← Array.index_mut_usize factors24 4#usize
  let a69 ←
    Array.update a68 4#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, x7, y7, q101 ] : Array
      aspis_core.field.QM31 4#usize)
  let _ ← host_weights.double y7
  ok (index_mut_back24 a69)

theorem row4_total (factors : Factors) (z : Array Point 2#usize) : Total (row4 factors z) := by
  unfold row4
  apply PV_B2_C_ArrayTotal.bind _ _ (read _ _ (by decide))
  intro scp1
  apply PV_B2_C_ArrayTotal.bind _ _ (⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩)
  intro q97
  apply PV_B2_C_ArrayTotal.bind _ _ (borrow _ _ (by decide))
  rintro ⟨a60, index_mut_back20⟩
  apply PV_B2_C_ArrayTotal.bind _ _ (write _ _ _ (by decide))
  intro a61
  apply PV_B2_C_ArrayTotal.bind _ _ (PV_B2_C_WeightsTotal.double _)
  intro x4
  apply PV_B2_C_ArrayTotal.bind _ _ (PV_B2_C_WeightsTotal.double _)
  intro y4
  apply PV_B2_C_ArrayTotal.bind _ _ (⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩)
  intro q98
  apply PV_B2_C_ArrayTotal.bind _ _ (borrow _ _ (by decide))
  rintro ⟨a62, index_mut_back21⟩
  apply PV_B2_C_ArrayTotal.bind _ _ (write _ _ _ (by decide))
  intro a63
  apply PV_B2_C_ArrayTotal.bind _ _ (PV_B2_C_WeightsTotal.double _)
  intro x5
  apply PV_B2_C_ArrayTotal.bind _ _ (PV_B2_C_WeightsTotal.double _)
  intro y5
  apply PV_B2_C_ArrayTotal.bind _ _ (⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩)
  intro q99
  apply PV_B2_C_ArrayTotal.bind _ _ (borrow _ _ (by decide))
  rintro ⟨a64, index_mut_back22⟩
  apply PV_B2_C_ArrayTotal.bind _ _ (write _ _ _ (by decide))
  intro a65
  apply PV_B2_C_ArrayTotal.bind _ _ (PV_B2_C_WeightsTotal.double _)
  intro x6
  apply PV_B2_C_ArrayTotal.bind _ _ (PV_B2_C_WeightsTotal.double _)
  intro y6
  apply PV_B2_C_ArrayTotal.bind _ _ (⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩)
  intro q100
  apply PV_B2_C_ArrayTotal.bind _ _ (borrow _ _ (by decide))
  rintro ⟨a66, index_mut_back23⟩
  apply PV_B2_C_ArrayTotal.bind _ _ (write _ _ _ (by decide))
  intro a67
  apply PV_B2_C_ArrayTotal.bind _ _ (PV_B2_C_WeightsTotal.double _)
  intro x7
  apply PV_B2_C_ArrayTotal.bind _ _ (PV_B2_C_WeightsTotal.double _)
  intro y7
  apply PV_B2_C_ArrayTotal.bind _ _ (⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩)
  intro q101
  apply PV_B2_C_ArrayTotal.bind _ _ (borrow _ _ (by decide))
  rintro ⟨a68, index_mut_back24⟩
  apply PV_B2_C_ArrayTotal.bind _ _ (write _ _ _ (by decide))
  intro a69
  apply PV_B2_C_ArrayTotal.bind _ _ (PV_B2_C_WeightsTotal.double _)
  intro unused
  exact ⟨_,rfl⟩
#print axioms row4_total
end PV_B2_C_ConstructorRows
