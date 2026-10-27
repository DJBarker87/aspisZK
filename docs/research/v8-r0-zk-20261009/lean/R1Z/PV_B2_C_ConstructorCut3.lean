import R1Z.PV_B2_C_ConstructorCut4
set_option autoImplicit false
namespace PV_B2_C_ConstructorCuts
open Aeneas Aeneas.Std Result PV_B2_C_ArrayTotal
open PV_B2_C_WeightsNative PV_B2_C_ConstructorRows
def flat3 (variant : transport.Variant) (points : Points) (q q1 : K) (z : Array Point 2#usize) (prevBack : FactorRow → Factors) (prevRow : FactorRow) : Result (core.result.Result host_weights.Weights verifier.Error) := do
  let scp ← Array.index_usize z 0#usize
  let q92 ← aspis_core.field.QM31.mul scp.x scp.y
  let factors15 := prevBack prevRow
  let (a50, index_mut_back15) ← Array.index_mut_usize factors15 3#usize
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
  let scp1 ← Array.index_usize z 1#usize
  let q97 ← aspis_core.field.QM31.mul scp1.x scp1.y
  let factors20 := index_mut_back19 a59
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
def cut3 (variant : transport.Variant) (points : Points) (q q1 : K) (z : Array Point 2#usize) (prevBack : FactorRow → Factors) (prevRow : FactorRow) : Result (core.result.Result host_weights.Weights verifier.Error) := do
  let scp ← Array.index_usize z 0#usize
  let q92 ← aspis_core.field.QM31.mul scp.x scp.y
  let factors15 := prevBack prevRow
  let (a50, index_mut_back15) ← Array.index_mut_usize factors15 3#usize
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
  flat4 variant points q q1 z index_mut_back19 a59

/-- Only one fixed-row prefix is compared; the remaining flat suffix is identical. -/
theorem flat3_eq_cut3 (variant : transport.Variant) (points : Points) (q q1 : K) (z : Array Point 2#usize) (prevBack : FactorRow → Factors) (prevRow : FactorRow) : flat3 variant points q q1 z prevBack prevRow = cut3 variant points q q1 z prevBack prevRow := by
  rfl

theorem cut3_total (variant : transport.Variant) (points : Points) (q q1 : K) (z : Array Point 2#usize) (prevBack : FactorRow → Factors) (prevRow : FactorRow) : RustOk (cut3 variant points q q1 z prevBack prevRow) := by
  unfold cut3
  apply bind_rust _ _ (read _ _ (by decide))
  intro scp
  apply bind_rust _ _ (⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩)
  intro q92
  apply bind_rust _ _ (borrow _ _ (by decide))
  rintro ⟨a50, index_mut_back15⟩
  apply bind_rust _ _ (write _ _ _ (by decide))
  intro a51
  apply bind_rust _ _ (PV_B2_C_WeightsTotal.double _)
  intro x
  apply bind_rust _ _ (PV_B2_C_WeightsTotal.double _)
  intro y
  apply bind_rust _ _ (⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩)
  intro q93
  apply bind_rust _ _ (borrow _ _ (by decide))
  rintro ⟨a52, index_mut_back16⟩
  apply bind_rust _ _ (write _ _ _ (by decide))
  intro a53
  apply bind_rust _ _ (PV_B2_C_WeightsTotal.double _)
  intro x1
  apply bind_rust _ _ (PV_B2_C_WeightsTotal.double _)
  intro y1
  apply bind_rust _ _ (⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩)
  intro q94
  apply bind_rust _ _ (borrow _ _ (by decide))
  rintro ⟨a54, index_mut_back17⟩
  apply bind_rust _ _ (write _ _ _ (by decide))
  intro a55
  apply bind_rust _ _ (PV_B2_C_WeightsTotal.double _)
  intro x2
  apply bind_rust _ _ (PV_B2_C_WeightsTotal.double _)
  intro y2
  apply bind_rust _ _ (⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩)
  intro q95
  apply bind_rust _ _ (borrow _ _ (by decide))
  rintro ⟨a56, index_mut_back18⟩
  apply bind_rust _ _ (write _ _ _ (by decide))
  intro a57
  apply bind_rust _ _ (PV_B2_C_WeightsTotal.double _)
  intro x3
  apply bind_rust _ _ (PV_B2_C_WeightsTotal.double _)
  intro y3
  apply bind_rust _ _ (⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩)
  intro q96
  apply bind_rust _ _ (borrow _ _ (by decide))
  rintro ⟨a58, index_mut_back19⟩
  apply bind_rust _ _ (write _ _ _ (by decide))
  intro a59
  apply bind_rust _ _ (PV_B2_C_WeightsTotal.double _)
  intro unused0
  exact flat4_total variant points q q1 z _ _

theorem flat3_total (variant : transport.Variant) (points : Points) (q q1 : K) (z : Array Point 2#usize) (prevBack : FactorRow → Factors) (prevRow : FactorRow) : RustOk (flat3 variant points q q1 z prevBack prevRow) := by
  rw [flat3_eq_cut3]
  exact cut3_total variant points q q1 z prevBack prevRow
#print axioms flat3_eq_cut3
#print axioms cut3_total
#print axioms flat3_total
end PV_B2_C_ConstructorCuts
