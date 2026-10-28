import R1Z.PV_RDB2C_PV_B2_C_Row3Cps
set_option autoImplicit false
namespace PV_B2_C_ConstructorRows
open Aeneas Aeneas.Std Result PV_B2_C_WeightsNative
/-- Fixed row 4: reassociation with an arbitrary Result continuation only. -/
theorem row4_cps {α : Type} (factors : Factors) (z : Array Point 2#usize)
    (k : Factors → Result α) :
    (row4 factors z >>= k) = (do
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
  k (index_mut_back24 a69)
) := by
  unfold row4
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back24 a69)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro scp1 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back24 a69)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q97 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back24 a69)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a60, index_mut_back20⟩ _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back24 a69)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a61 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back24 a69)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro x4 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back24 a69)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro y4 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back24 a69)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q98 _
  let factors21 := index_mut_back20 a61
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back24 a69)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a62, index_mut_back21⟩ _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back24 a69)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a63 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back24 a69)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro x5 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back24 a69)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro y5 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back24 a69)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q99 _
  let factors22 := index_mut_back21 a63
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back24 a69)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a64, index_mut_back22⟩ _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back24 a69)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a65 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back24 a69)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro x6 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back24 a69)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro y6 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back24 a69)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q100 _
  let factors23 := index_mut_back22 a65
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back24 a69)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a66, index_mut_back23⟩ _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back24 a69)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a67 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back24 a69)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro x7 _
  change ((do
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
) >>= k) = (do
  let y7 ← host_weights.double x7
  let q101 ← aspis_core.field.QM31.mul x7 y7
  let factors24 := index_mut_back23 a67
  let (a68, index_mut_back24) ← Array.index_mut_usize factors24 4#usize
  let a69 ←
    Array.update a68 4#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, x7, y7, q101 ] : Array
      aspis_core.field.QM31 4#usize)
  let _ ← host_weights.double y7
  k (index_mut_back24 a69)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro y7 _
  change ((do
  let q101 ← aspis_core.field.QM31.mul x7 y7
  let factors24 := index_mut_back23 a67
  let (a68, index_mut_back24) ← Array.index_mut_usize factors24 4#usize
  let a69 ←
    Array.update a68 4#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, x7, y7, q101 ] : Array
      aspis_core.field.QM31 4#usize)
  let _ ← host_weights.double y7
  ok (index_mut_back24 a69)
) >>= k) = (do
  let q101 ← aspis_core.field.QM31.mul x7 y7
  let factors24 := index_mut_back23 a67
  let (a68, index_mut_back24) ← Array.index_mut_usize factors24 4#usize
  let a69 ←
    Array.update a68 4#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, x7, y7, q101 ] : Array
      aspis_core.field.QM31 4#usize)
  let _ ← host_weights.double y7
  k (index_mut_back24 a69)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q101 _
  let factors24 := index_mut_back23 a67
  change ((do
  let (a68, index_mut_back24) ← Array.index_mut_usize factors24 4#usize
  let a69 ←
    Array.update a68 4#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, x7, y7, q101 ] : Array
      aspis_core.field.QM31 4#usize)
  let _ ← host_weights.double y7
  ok (index_mut_back24 a69)
) >>= k) = (do
  let (a68, index_mut_back24) ← Array.index_mut_usize factors24 4#usize
  let a69 ←
    Array.update a68 4#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, x7, y7, q101 ] : Array
      aspis_core.field.QM31 4#usize)
  let _ ← host_weights.double y7
  k (index_mut_back24 a69)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a68, index_mut_back24⟩ _
  change ((do
  let a69 ←
    Array.update a68 4#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, x7, y7, q101 ] : Array
      aspis_core.field.QM31 4#usize)
  let _ ← host_weights.double y7
  ok (index_mut_back24 a69)
) >>= k) = (do
  let a69 ←
    Array.update a68 4#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, x7, y7, q101 ] : Array
      aspis_core.field.QM31 4#usize)
  let _ ← host_weights.double y7
  k (index_mut_back24 a69)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a69 _
  change ((do
  let _ ← host_weights.double y7
  ok (index_mut_back24 a69)
) >>= k) = (do
  let _ ← host_weights.double y7
  k (index_mut_back24 a69)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro unused _
  exact bind_tc_ok _ _
#print axioms row4_cps
end PV_B2_C_ConstructorRows
