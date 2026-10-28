import R1Z.PV_RDB2C_PV_B2_C_ConstructorRow0
set_option autoImplicit false
noncomputable section
namespace PV_B2_C_ConstructorRows
open Aeneas Aeneas.Std Result PV_B2_C_ArrayTotal PV_B2_C_WeightsNative

/-- Exact fixed factor row 1; all array restorations are retained. -/
def row1 (factors : Factors) (points : Points) : Result Factors := do
  let a18 ← Array.index_usize points 1#usize
  let a19 ← Array.index_usize a18 3#usize
  let b5 ← Array.index_usize a18 2#usize
  let q32 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a19
  let q33 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b5
  let q34 ← aspis_core.field.QM31.mul q32 q33
  let q35 ← aspis_core.field.QM31.mul a19 q33
  let q36 ← aspis_core.field.QM31.mul q32 b5
  let q37 ← aspis_core.field.QM31.mul a19 b5
  let (a20, index_mut_back5) ← Array.index_mut_usize factors 1#usize
  let a21 ←
    Array.update a20 0#usize (Array.make 4#usize [ q34, q35, q36, q37 ] : Array
      aspis_core.field.QM31 4#usize)
  let a22 ← Array.index_usize a18 1#usize
  let b6 ← Array.index_usize a18 0#usize
  let q38 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a22
  let q39 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b6
  let q40 ← aspis_core.field.QM31.mul q38 q39
  let q41 ← aspis_core.field.QM31.mul a22 q39
  let q42 ← aspis_core.field.QM31.mul q38 b6
  let q43 ← aspis_core.field.QM31.mul a22 b6
  let factors6 := index_mut_back5 a21
  let (a23, index_mut_back6) ← Array.index_mut_usize factors6 1#usize
  let a24 ←
    Array.update a23 1#usize (Array.make 4#usize [ q40, q41, q42, q43 ] : Array
      aspis_core.field.QM31 4#usize)
  let a25 ← Array.index_usize a18 5#usize
  let b7 ← Array.index_usize a18 4#usize
  let q44 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a25
  let q45 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b7
  let q46 ← aspis_core.field.QM31.mul q44 q45
  let q47 ← aspis_core.field.QM31.mul a25 q45
  let q48 ← aspis_core.field.QM31.mul q44 b7
  let q49 ← aspis_core.field.QM31.mul a25 b7
  let factors7 := index_mut_back6 a24
  let (a26, index_mut_back7) ← Array.index_mut_usize factors7 1#usize
  let a27 ←
    Array.update a26 2#usize (Array.make 4#usize [ q46, q47, q48, q49 ] : Array
      aspis_core.field.QM31 4#usize)
  let a28 ← Array.index_usize a18 9#usize
  let b8 ← Array.index_usize a18 8#usize
  let q50 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a28
  let q51 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b8
  let q52 ← aspis_core.field.QM31.mul q50 q51
  let q53 ← aspis_core.field.QM31.mul a28 q51
  let q54 ← aspis_core.field.QM31.mul q50 b8
  let q55 ← aspis_core.field.QM31.mul a28 b8
  let factors8 := index_mut_back7 a27
  let (a29, index_mut_back8) ← Array.index_mut_usize factors8 1#usize
  let a30 ←
    Array.update a29 3#usize (Array.make 4#usize [ q52, q53, q54, q55 ] : Array
      aspis_core.field.QM31 4#usize)
  let a31 ← Array.index_usize a18 7#usize
  let b9 ← Array.index_usize a18 6#usize
  let q56 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a31
  let q57 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b9
  let q58 ← aspis_core.field.QM31.mul q56 q57
  let q59 ← aspis_core.field.QM31.mul a31 q57
  let q60 ← aspis_core.field.QM31.mul q56 b9
  let q61 ← aspis_core.field.QM31.mul a31 b9
  let factors9 := index_mut_back8 a30
  let (a32, index_mut_back9) ← Array.index_mut_usize factors9 1#usize
  let a33 ←
    Array.update a32 4#usize (Array.make 4#usize [ q58, q59, q60, q61 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back9 a33)

theorem row1_total (factors : Factors) (points : Points) : Total (row1 factors points) := by
  unfold row1
  simp only [PV_B2_C_FieldTotal.QM31_mul,PV_B2_C_FieldTotal.QM31_add,
    PV_B2_C_FieldTotal.QM31_sub,bind_tc_ok]
  repeat' first
    | exact ⟨_,rfl⟩
    | exact read _ _ (by decide)
    | exact write _ _ _ (by decide)
    | exact borrow _ _ (by decide)
    | exact PV_B2_C_WeightsTotal.double _
    | apply PV_B2_C_ArrayTotal.bind
    | (intro x; cases x)
#print axioms row1_total
end PV_B2_C_ConstructorRows
