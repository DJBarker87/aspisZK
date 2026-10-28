import R1Z.PV_RDB2C_PV_B2_C_ConstructorRow2
set_option autoImplicit false
noncomputable section
namespace PV_B2_C_ConstructorRows
open Aeneas Aeneas.Std Result PV_B2_C_ArrayTotal PV_B2_C_WeightsNative

/-- Exact fixed factor row 3; all array restorations are retained. -/
def row3 (factors : Factors) (z : Array Point 2#usize) : Result Factors := do
  let scp ← Array.index_usize z 0#usize
  let q92 ← aspis_core.field.QM31.mul scp.x scp.y
  let (a50, index_mut_back15) ← Array.index_mut_usize factors 3#usize
  let a51 ←
    Array.update a50 0#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, scp.y, scp.x, q92 ] :
      Array aspis_core.field.QM31 4#usize)
  let x ← host_weights.double scp.x
  let y ← host_weights.double x
  let q93 ← aspis_core.field.QM31.mul x y
  let factors16 := index_mut_back15 a51
  let (a52, index_mut_back16) ← Array.index_mut_usize factors16 3#usize
  let a53 ←
    Array.update a52 1#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, x, y, q93 ] : Array
      aspis_core.field.QM31 4#usize)
  let x1 ← host_weights.double y
  let y1 ← host_weights.double x1
  let q94 ← aspis_core.field.QM31.mul x1 y1
  let factors17 := index_mut_back16 a53
  let (a54, index_mut_back17) ← Array.index_mut_usize factors17 3#usize
  let a55 ←
    Array.update a54 2#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, x1, y1, q94 ] : Array
      aspis_core.field.QM31 4#usize)
  let x2 ← host_weights.double y1
  let y2 ← host_weights.double x2
  let q95 ← aspis_core.field.QM31.mul x2 y2
  let factors18 := index_mut_back17 a55
  let (a56, index_mut_back18) ← Array.index_mut_usize factors18 3#usize
  let a57 ←
    Array.update a56 3#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, x2, y2, q95 ] : Array
      aspis_core.field.QM31 4#usize)
  let x3 ← host_weights.double y2
  let y3 ← host_weights.double x3
  let q96 ← aspis_core.field.QM31.mul x3 y3
  let factors19 := index_mut_back18 a57
  let (a58, index_mut_back19) ← Array.index_mut_usize factors19 3#usize
  let a59 ←
    Array.update a58 4#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, x3, y3, q96 ] : Array
      aspis_core.field.QM31 4#usize)
  let _ ← host_weights.double y3
  ok (index_mut_back19 a59)

theorem row3_total (factors : Factors) (z : Array Point 2#usize) : Total (row3 factors z) := by
  unfold row3
  apply PV_B2_C_ArrayTotal.bind _ _ (read _ _ (by decide))
  intro scp
  apply PV_B2_C_ArrayTotal.bind _ _ (⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩)
  intro q92
  apply PV_B2_C_ArrayTotal.bind _ _ (borrow _ _ (by decide))
  rintro ⟨a50, index_mut_back15⟩
  apply PV_B2_C_ArrayTotal.bind _ _ (write _ _ _ (by decide))
  intro a51
  apply PV_B2_C_ArrayTotal.bind _ _ (PV_B2_C_WeightsTotal.double _)
  intro x
  apply PV_B2_C_ArrayTotal.bind _ _ (PV_B2_C_WeightsTotal.double _)
  intro y
  apply PV_B2_C_ArrayTotal.bind _ _ (⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩)
  intro q93
  apply PV_B2_C_ArrayTotal.bind _ _ (borrow _ _ (by decide))
  rintro ⟨a52, index_mut_back16⟩
  apply PV_B2_C_ArrayTotal.bind _ _ (write _ _ _ (by decide))
  intro a53
  apply PV_B2_C_ArrayTotal.bind _ _ (PV_B2_C_WeightsTotal.double _)
  intro x1
  apply PV_B2_C_ArrayTotal.bind _ _ (PV_B2_C_WeightsTotal.double _)
  intro y1
  apply PV_B2_C_ArrayTotal.bind _ _ (⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩)
  intro q94
  apply PV_B2_C_ArrayTotal.bind _ _ (borrow _ _ (by decide))
  rintro ⟨a54, index_mut_back17⟩
  apply PV_B2_C_ArrayTotal.bind _ _ (write _ _ _ (by decide))
  intro a55
  apply PV_B2_C_ArrayTotal.bind _ _ (PV_B2_C_WeightsTotal.double _)
  intro x2
  apply PV_B2_C_ArrayTotal.bind _ _ (PV_B2_C_WeightsTotal.double _)
  intro y2
  apply PV_B2_C_ArrayTotal.bind _ _ (⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩)
  intro q95
  apply PV_B2_C_ArrayTotal.bind _ _ (borrow _ _ (by decide))
  rintro ⟨a56, index_mut_back18⟩
  apply PV_B2_C_ArrayTotal.bind _ _ (write _ _ _ (by decide))
  intro a57
  apply PV_B2_C_ArrayTotal.bind _ _ (PV_B2_C_WeightsTotal.double _)
  intro x3
  apply PV_B2_C_ArrayTotal.bind _ _ (PV_B2_C_WeightsTotal.double _)
  intro y3
  apply PV_B2_C_ArrayTotal.bind _ _ (⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩)
  intro q96
  apply PV_B2_C_ArrayTotal.bind _ _ (borrow _ _ (by decide))
  rintro ⟨a58, index_mut_back19⟩
  apply PV_B2_C_ArrayTotal.bind _ _ (write _ _ _ (by decide))
  intro a59
  apply PV_B2_C_ArrayTotal.bind _ _ (PV_B2_C_WeightsTotal.double _)
  intro unused
  exact ⟨_,rfl⟩
#print axioms row3_total
end PV_B2_C_ConstructorRows
