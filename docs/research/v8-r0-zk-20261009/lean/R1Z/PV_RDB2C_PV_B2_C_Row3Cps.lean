import R1Z.PV_RDB2C_PV_B2_C_Row2Cps
set_option autoImplicit false
namespace PV_B2_C_ConstructorRows
open Aeneas Aeneas.Std Result PV_B2_C_WeightsNative
/-- Fixed row 3: reassociation with an arbitrary Result continuation only. -/
theorem row3_cps {α : Type} (factors : Factors) (z : Array Point 2#usize)
    (k : Factors → Result α) :
    (row3 factors z >>= k) = (do
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
  k (index_mut_back19 a59)
) := by
  unfold row3
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back19 a59)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro scp _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back19 a59)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q92 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back19 a59)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a50, index_mut_back15⟩ _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back19 a59)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a51 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back19 a59)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro x _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back19 a59)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro y _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back19 a59)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q93 _
  let factors16 := index_mut_back15 a51
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back19 a59)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a52, index_mut_back16⟩ _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back19 a59)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a53 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back19 a59)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro x1 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back19 a59)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro y1 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back19 a59)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q94 _
  let factors17 := index_mut_back16 a53
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back19 a59)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a54, index_mut_back17⟩ _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back19 a59)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a55 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back19 a59)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro x2 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back19 a59)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro y2 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back19 a59)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q95 _
  let factors18 := index_mut_back17 a55
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back19 a59)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a56, index_mut_back18⟩ _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back19 a59)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a57 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back19 a59)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro x3 _
  change ((do
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
) >>= k) = (do
  let y3 ← host_weights.double x3
  let q96 ← aspis_core.field.QM31.mul x3 y3
  let factors19 := index_mut_back18 a57
  let (a58, index_mut_back19) ← Array.index_mut_usize factors19 3#usize
  let a59 ←
    Array.update a58 4#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, x3, y3, q96 ] : Array
      aspis_core.field.QM31 4#usize)
  let _ ← host_weights.double y3
  k (index_mut_back19 a59)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro y3 _
  change ((do
  let q96 ← aspis_core.field.QM31.mul x3 y3
  let factors19 := index_mut_back18 a57
  let (a58, index_mut_back19) ← Array.index_mut_usize factors19 3#usize
  let a59 ←
    Array.update a58 4#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, x3, y3, q96 ] : Array
      aspis_core.field.QM31 4#usize)
  let _ ← host_weights.double y3
  ok (index_mut_back19 a59)
) >>= k) = (do
  let q96 ← aspis_core.field.QM31.mul x3 y3
  let factors19 := index_mut_back18 a57
  let (a58, index_mut_back19) ← Array.index_mut_usize factors19 3#usize
  let a59 ←
    Array.update a58 4#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, x3, y3, q96 ] : Array
      aspis_core.field.QM31 4#usize)
  let _ ← host_weights.double y3
  k (index_mut_back19 a59)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q96 _
  let factors19 := index_mut_back18 a57
  change ((do
  let (a58, index_mut_back19) ← Array.index_mut_usize factors19 3#usize
  let a59 ←
    Array.update a58 4#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, x3, y3, q96 ] : Array
      aspis_core.field.QM31 4#usize)
  let _ ← host_weights.double y3
  ok (index_mut_back19 a59)
) >>= k) = (do
  let (a58, index_mut_back19) ← Array.index_mut_usize factors19 3#usize
  let a59 ←
    Array.update a58 4#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, x3, y3, q96 ] : Array
      aspis_core.field.QM31 4#usize)
  let _ ← host_weights.double y3
  k (index_mut_back19 a59)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a58, index_mut_back19⟩ _
  change ((do
  let a59 ←
    Array.update a58 4#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, x3, y3, q96 ] : Array
      aspis_core.field.QM31 4#usize)
  let _ ← host_weights.double y3
  ok (index_mut_back19 a59)
) >>= k) = (do
  let a59 ←
    Array.update a58 4#usize
      (Array.make 4#usize [ aspis_core.field.QM31.ONE, x3, y3, q96 ] : Array
      aspis_core.field.QM31 4#usize)
  let _ ← host_weights.double y3
  k (index_mut_back19 a59)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a59 _
  change ((do
  let _ ← host_weights.double y3
  ok (index_mut_back19 a59)
) >>= k) = (do
  let _ ← host_weights.double y3
  k (index_mut_back19 a59)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro unused _
  exact bind_tc_ok _ _
#print axioms row3_cps
end PV_B2_C_ConstructorRows
