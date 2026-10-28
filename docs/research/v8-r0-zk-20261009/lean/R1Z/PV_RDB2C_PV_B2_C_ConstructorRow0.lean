import R1Z.PV_RDB2C_PV_B2_C_ConstructorEnvironment
set_option autoImplicit false
noncomputable section
namespace PV_B2_C_ConstructorRows
open Aeneas Aeneas.Std Result PV_B2_C_ArrayTotal PV_B2_C_WeightsNative
abbrev K := PV_B2_C_Carrier.aspis_core.field.QM31
abbrev Point := PV_B2_C_Carrier.aspis_core.circle.SecureCirclePoint
abbrev Factors := Array (Array (Array K 4#usize) 5#usize) 5#usize
abbrev Points := Array (Array K 10#usize) 3#usize

/-- Exact fixed factor row 0; all array restorations are retained. -/
def row0 (factors : Factors) (points : Points) : Result Factors := do
  let a2 ← Array.index_usize points 0#usize
  let a3 ← Array.index_usize a2 3#usize
  let b ← Array.index_usize a2 2#usize
  let q2 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a3
  let q3 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b
  let q4 ← aspis_core.field.QM31.mul q2 q3
  let q5 ← aspis_core.field.QM31.mul a3 q3
  let q6 ← aspis_core.field.QM31.mul q2 b
  let q7 ← aspis_core.field.QM31.mul a3 b
  let (a4, index_mut_back) ← Array.index_mut_usize factors 0#usize
  let a5 ←
    Array.update a4 0#usize (Array.make 4#usize [ q4, q5, q6, q7 ] : Array
      aspis_core.field.QM31 4#usize)
  let a6 ← Array.index_usize a2 1#usize
  let b1 ← Array.index_usize a2 0#usize
  let q8 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a6
  let q9 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b1
  let q10 ← aspis_core.field.QM31.mul q8 q9
  let q11 ← aspis_core.field.QM31.mul a6 q9
  let q12 ← aspis_core.field.QM31.mul q8 b1
  let q13 ← aspis_core.field.QM31.mul a6 b1
  let factors1 := index_mut_back a5
  let (a7, index_mut_back1) ← Array.index_mut_usize factors1 0#usize
  let a8 ←
    Array.update a7 1#usize (Array.make 4#usize [ q10, q11, q12, q13 ] : Array
      aspis_core.field.QM31 4#usize)
  let a9 ← Array.index_usize a2 5#usize
  let b2 ← Array.index_usize a2 4#usize
  let q14 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a9
  let q15 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b2
  let q16 ← aspis_core.field.QM31.mul q14 q15
  let q17 ← aspis_core.field.QM31.mul a9 q15
  let q18 ← aspis_core.field.QM31.mul q14 b2
  let q19 ← aspis_core.field.QM31.mul a9 b2
  let factors2 := index_mut_back1 a8
  let (a10, index_mut_back2) ← Array.index_mut_usize factors2 0#usize
  let a11 ←
    Array.update a10 2#usize (Array.make 4#usize [ q16, q17, q18, q19 ] : Array
      aspis_core.field.QM31 4#usize)
  let a12 ← Array.index_usize a2 9#usize
  let b3 ← Array.index_usize a2 8#usize
  let q20 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a12
  let q21 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b3
  let q22 ← aspis_core.field.QM31.mul q20 q21
  let q23 ← aspis_core.field.QM31.mul a12 q21
  let q24 ← aspis_core.field.QM31.mul q20 b3
  let q25 ← aspis_core.field.QM31.mul a12 b3
  let factors3 := index_mut_back2 a11
  let (a13, index_mut_back3) ← Array.index_mut_usize factors3 0#usize
  let a14 ←
    Array.update a13 3#usize (Array.make 4#usize [ q22, q23, q24, q25 ] : Array
      aspis_core.field.QM31 4#usize)
  let a15 ← Array.index_usize a2 7#usize
  let b4 ← Array.index_usize a2 6#usize
  let q26 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a15
  let q27 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b4
  let q28 ← aspis_core.field.QM31.mul q26 q27
  let q29 ← aspis_core.field.QM31.mul a15 q27
  let q30 ← aspis_core.field.QM31.mul q26 b4
  let q31 ← aspis_core.field.QM31.mul a15 b4
  let factors4 := index_mut_back3 a14
  let (a16, index_mut_back4) ← Array.index_mut_usize factors4 0#usize
  let a17 ←
    Array.update a16 4#usize (Array.make 4#usize [ q28, q29, q30, q31 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back4 a17)

theorem row0_total (factors : Factors) (points : Points) : Total (row0 factors points) := by
  unfold row0
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
#print axioms row0_total
end PV_B2_C_ConstructorRows
