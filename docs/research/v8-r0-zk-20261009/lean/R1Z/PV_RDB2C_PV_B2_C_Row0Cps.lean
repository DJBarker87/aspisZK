import R1Z.PV_RDB2C_PV_B2_C_ConstructorRow4
set_option autoImplicit false
namespace PV_B2_C_ConstructorRows
open Aeneas Aeneas.Std Result PV_B2_C_WeightsNative
/-- Fixed row 0: reassociation with an arbitrary Result continuation only. -/
theorem row0_cps {α : Type} (factors : Factors) (points : Points)
    (k : Factors → Result α) :
    (row0 factors points >>= k) = (do
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
  k (index_mut_back4 a17)
) := by
  unfold row0
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a2 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a3 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro b _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q2 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q3 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q4 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q5 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q6 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q7 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a4, index_mut_back⟩ _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a5 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a6 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro b1 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q8 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q9 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q10 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q11 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q12 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q13 _
  let factors1 := index_mut_back a5
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a7, index_mut_back1⟩ _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a8 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a9 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro b2 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q14 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q15 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q16 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q17 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q18 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q19 _
  let factors2 := index_mut_back1 a8
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a10, index_mut_back2⟩ _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a11 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a12 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro b3 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q20 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q21 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q22 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q23 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q24 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q25 _
  let factors3 := index_mut_back2 a11
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a13, index_mut_back3⟩ _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a14 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a15 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro b4 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q26 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q27 _
  change ((do
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
) >>= k) = (do
  let q28 ← aspis_core.field.QM31.mul q26 q27
  let q29 ← aspis_core.field.QM31.mul a15 q27
  let q30 ← aspis_core.field.QM31.mul q26 b4
  let q31 ← aspis_core.field.QM31.mul a15 b4
  let factors4 := index_mut_back3 a14
  let (a16, index_mut_back4) ← Array.index_mut_usize factors4 0#usize
  let a17 ←
    Array.update a16 4#usize (Array.make 4#usize [ q28, q29, q30, q31 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q28 _
  change ((do
  let q29 ← aspis_core.field.QM31.mul a15 q27
  let q30 ← aspis_core.field.QM31.mul q26 b4
  let q31 ← aspis_core.field.QM31.mul a15 b4
  let factors4 := index_mut_back3 a14
  let (a16, index_mut_back4) ← Array.index_mut_usize factors4 0#usize
  let a17 ←
    Array.update a16 4#usize (Array.make 4#usize [ q28, q29, q30, q31 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back4 a17)
) >>= k) = (do
  let q29 ← aspis_core.field.QM31.mul a15 q27
  let q30 ← aspis_core.field.QM31.mul q26 b4
  let q31 ← aspis_core.field.QM31.mul a15 b4
  let factors4 := index_mut_back3 a14
  let (a16, index_mut_back4) ← Array.index_mut_usize factors4 0#usize
  let a17 ←
    Array.update a16 4#usize (Array.make 4#usize [ q28, q29, q30, q31 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q29 _
  change ((do
  let q30 ← aspis_core.field.QM31.mul q26 b4
  let q31 ← aspis_core.field.QM31.mul a15 b4
  let factors4 := index_mut_back3 a14
  let (a16, index_mut_back4) ← Array.index_mut_usize factors4 0#usize
  let a17 ←
    Array.update a16 4#usize (Array.make 4#usize [ q28, q29, q30, q31 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back4 a17)
) >>= k) = (do
  let q30 ← aspis_core.field.QM31.mul q26 b4
  let q31 ← aspis_core.field.QM31.mul a15 b4
  let factors4 := index_mut_back3 a14
  let (a16, index_mut_back4) ← Array.index_mut_usize factors4 0#usize
  let a17 ←
    Array.update a16 4#usize (Array.make 4#usize [ q28, q29, q30, q31 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q30 _
  change ((do
  let q31 ← aspis_core.field.QM31.mul a15 b4
  let factors4 := index_mut_back3 a14
  let (a16, index_mut_back4) ← Array.index_mut_usize factors4 0#usize
  let a17 ←
    Array.update a16 4#usize (Array.make 4#usize [ q28, q29, q30, q31 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back4 a17)
) >>= k) = (do
  let q31 ← aspis_core.field.QM31.mul a15 b4
  let factors4 := index_mut_back3 a14
  let (a16, index_mut_back4) ← Array.index_mut_usize factors4 0#usize
  let a17 ←
    Array.update a16 4#usize (Array.make 4#usize [ q28, q29, q30, q31 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q31 _
  let factors4 := index_mut_back3 a14
  change ((do
  let (a16, index_mut_back4) ← Array.index_mut_usize factors4 0#usize
  let a17 ←
    Array.update a16 4#usize (Array.make 4#usize [ q28, q29, q30, q31 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back4 a17)
) >>= k) = (do
  let (a16, index_mut_back4) ← Array.index_mut_usize factors4 0#usize
  let a17 ←
    Array.update a16 4#usize (Array.make 4#usize [ q28, q29, q30, q31 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a16, index_mut_back4⟩ _
  change ((do
  let a17 ←
    Array.update a16 4#usize (Array.make 4#usize [ q28, q29, q30, q31 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back4 a17)
) >>= k) = (do
  let a17 ←
    Array.update a16 4#usize (Array.make 4#usize [ q28, q29, q30, q31 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back4 a17)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a17 _
  exact bind_tc_ok _ _
#print axioms row0_cps
end PV_B2_C_ConstructorRows
