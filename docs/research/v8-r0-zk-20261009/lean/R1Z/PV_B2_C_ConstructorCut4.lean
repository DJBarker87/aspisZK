import R1Z.PV_B2_C_ConstructorRow4
set_option autoImplicit false
namespace PV_B2_C_ConstructorCuts
open Aeneas Aeneas.Std Result PV_B2_C_ArrayTotal
open PV_B2_C_WeightsNative PV_B2_C_ConstructorRows
abbrev FactorRow := Array (Array K 4#usize) 5#usize
def flat4 (variant : transport.Variant) (points : Points) (q q1 : K) (z : Array Point 2#usize) (prevBack : FactorRow → Factors) (prevRow : FactorRow) : Result (core.result.Result host_weights.Weights verifier.Error) := do
  let scp1 ← Array.index_usize z 1#usize
  let q97 ← aspis_core.field.QM31.mul scp1.x scp1.y
  let factors20 := prevBack prevRow
  let (a60, index_mut_back20) ← Array.index_mut_usize factors20 4#usize
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
  let factors25 := index_mut_back24 a69
  ok (core.result.Result.Ok
    {
      variant,
      factors := factors25,
      points,
      extra := (Array.make 2#usize [ q, q1 ])
    })
def cut4 (variant : transport.Variant) (points : Points) (q q1 : K) (z : Array Point 2#usize) (prevBack : FactorRow → Factors) (prevRow : FactorRow) : Result (core.result.Result host_weights.Weights verifier.Error) := do
  let scp1 ← Array.index_usize z 1#usize
  let q97 ← aspis_core.field.QM31.mul scp1.x scp1.y
  let factors20 := prevBack prevRow
  let (a60, index_mut_back20) ← Array.index_mut_usize factors20 4#usize
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
  let factors25 := index_mut_back24 a69
  ok (core.result.Result.Ok
    {
      variant,
      factors := factors25,
      points,
      extra := (Array.make 2#usize [ q, q1 ])
    })
/-- Only one fixed-row prefix is compared; the remaining flat suffix is identical. -/
theorem flat4_eq_cut4 (variant : transport.Variant) (points : Points) (q q1 : K) (z : Array Point 2#usize) (prevBack : FactorRow → Factors) (prevRow : FactorRow) : flat4 variant points q q1 z prevBack prevRow = cut4 variant points q q1 z prevBack prevRow := by
  rfl

theorem cut4_total (variant : transport.Variant) (points : Points) (q q1 : K) (z : Array Point 2#usize) (prevBack : FactorRow → Factors) (prevRow : FactorRow) : RustOk (cut4 variant points q q1 z prevBack prevRow) := by
  unfold cut4
  apply bind_rust _ _ (read _ _ (by decide))
  intro scp1
  apply bind_rust _ _ (⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩)
  intro q97
  apply bind_rust _ _ (borrow _ _ (by decide))
  rintro ⟨a60, index_mut_back20⟩
  apply bind_rust _ _ (write _ _ _ (by decide))
  intro a61
  apply bind_rust _ _ (PV_B2_C_WeightsTotal.double _)
  intro x4
  apply bind_rust _ _ (PV_B2_C_WeightsTotal.double _)
  intro y4
  apply bind_rust _ _ (⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩)
  intro q98
  apply bind_rust _ _ (borrow _ _ (by decide))
  rintro ⟨a62, index_mut_back21⟩
  apply bind_rust _ _ (write _ _ _ (by decide))
  intro a63
  apply bind_rust _ _ (PV_B2_C_WeightsTotal.double _)
  intro x5
  apply bind_rust _ _ (PV_B2_C_WeightsTotal.double _)
  intro y5
  apply bind_rust _ _ (⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩)
  intro q99
  apply bind_rust _ _ (borrow _ _ (by decide))
  rintro ⟨a64, index_mut_back22⟩
  apply bind_rust _ _ (write _ _ _ (by decide))
  intro a65
  apply bind_rust _ _ (PV_B2_C_WeightsTotal.double _)
  intro x6
  apply bind_rust _ _ (PV_B2_C_WeightsTotal.double _)
  intro y6
  apply bind_rust _ _ (⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩)
  intro q100
  apply bind_rust _ _ (borrow _ _ (by decide))
  rintro ⟨a66, index_mut_back23⟩
  apply bind_rust _ _ (write _ _ _ (by decide))
  intro a67
  apply bind_rust _ _ (PV_B2_C_WeightsTotal.double _)
  intro x7
  apply bind_rust _ _ (PV_B2_C_WeightsTotal.double _)
  intro y7
  apply bind_rust _ _ (⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩)
  intro q101
  apply bind_rust _ _ (borrow _ _ (by decide))
  rintro ⟨a68, index_mut_back24⟩
  apply bind_rust _ _ (write _ _ _ (by decide))
  intro a69
  apply bind_rust _ _ (PV_B2_C_WeightsTotal.double _)
  intro unused0
  exact ⟨_,rfl⟩

theorem flat4_total (variant : transport.Variant) (points : Points) (q q1 : K) (z : Array Point 2#usize) (prevBack : FactorRow → Factors) (prevRow : FactorRow) : RustOk (flat4 variant points q q1 z prevBack prevRow) := by
  rw [flat4_eq_cut4]
  exact cut4_total variant points q q1 z prevBack prevRow
#print axioms flat4_eq_cut4
#print axioms cut4_total
#print axioms flat4_total
end PV_B2_C_ConstructorCuts
