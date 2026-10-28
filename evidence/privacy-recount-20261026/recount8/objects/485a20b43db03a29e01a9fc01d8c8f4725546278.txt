import R1Z.PV_RDB2C_PV_B2_C_Row0Cps
set_option autoImplicit false
namespace PV_B2_C_ConstructorRows
open Aeneas Aeneas.Std Result PV_B2_C_WeightsNative
/-- Fixed row 1: reassociation with an arbitrary Result continuation only. -/
theorem row1_cps {α : Type} (factors : Factors) (points : Points)
    (k : Factors → Result α) :
    (row1 factors points >>= k) = (do
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
  k (index_mut_back9 a33)
) := by
  unfold row1
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a18 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a19 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro b5 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q32 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q33 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q34 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q35 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q36 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q37 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a20, index_mut_back5⟩ _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a21 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a22 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro b6 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q38 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q39 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q40 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q41 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q42 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q43 _
  let factors6 := index_mut_back5 a21
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a23, index_mut_back6⟩ _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a24 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a25 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro b7 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q44 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q45 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q46 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q47 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q48 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q49 _
  let factors7 := index_mut_back6 a24
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a26, index_mut_back7⟩ _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a27 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a28 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro b8 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q50 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q51 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q52 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q53 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q54 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q55 _
  let factors8 := index_mut_back7 a27
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a29, index_mut_back8⟩ _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a30 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a31 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro b9 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q56 _
  change ((do
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
) >>= k) = (do
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
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q57 _
  change ((do
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
) >>= k) = (do
  let q58 ← aspis_core.field.QM31.mul q56 q57
  let q59 ← aspis_core.field.QM31.mul a31 q57
  let q60 ← aspis_core.field.QM31.mul q56 b9
  let q61 ← aspis_core.field.QM31.mul a31 b9
  let factors9 := index_mut_back8 a30
  let (a32, index_mut_back9) ← Array.index_mut_usize factors9 1#usize
  let a33 ←
    Array.update a32 4#usize (Array.make 4#usize [ q58, q59, q60, q61 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q58 _
  change ((do
  let q59 ← aspis_core.field.QM31.mul a31 q57
  let q60 ← aspis_core.field.QM31.mul q56 b9
  let q61 ← aspis_core.field.QM31.mul a31 b9
  let factors9 := index_mut_back8 a30
  let (a32, index_mut_back9) ← Array.index_mut_usize factors9 1#usize
  let a33 ←
    Array.update a32 4#usize (Array.make 4#usize [ q58, q59, q60, q61 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back9 a33)
) >>= k) = (do
  let q59 ← aspis_core.field.QM31.mul a31 q57
  let q60 ← aspis_core.field.QM31.mul q56 b9
  let q61 ← aspis_core.field.QM31.mul a31 b9
  let factors9 := index_mut_back8 a30
  let (a32, index_mut_back9) ← Array.index_mut_usize factors9 1#usize
  let a33 ←
    Array.update a32 4#usize (Array.make 4#usize [ q58, q59, q60, q61 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q59 _
  change ((do
  let q60 ← aspis_core.field.QM31.mul q56 b9
  let q61 ← aspis_core.field.QM31.mul a31 b9
  let factors9 := index_mut_back8 a30
  let (a32, index_mut_back9) ← Array.index_mut_usize factors9 1#usize
  let a33 ←
    Array.update a32 4#usize (Array.make 4#usize [ q58, q59, q60, q61 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back9 a33)
) >>= k) = (do
  let q60 ← aspis_core.field.QM31.mul q56 b9
  let q61 ← aspis_core.field.QM31.mul a31 b9
  let factors9 := index_mut_back8 a30
  let (a32, index_mut_back9) ← Array.index_mut_usize factors9 1#usize
  let a33 ←
    Array.update a32 4#usize (Array.make 4#usize [ q58, q59, q60, q61 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q60 _
  change ((do
  let q61 ← aspis_core.field.QM31.mul a31 b9
  let factors9 := index_mut_back8 a30
  let (a32, index_mut_back9) ← Array.index_mut_usize factors9 1#usize
  let a33 ←
    Array.update a32 4#usize (Array.make 4#usize [ q58, q59, q60, q61 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back9 a33)
) >>= k) = (do
  let q61 ← aspis_core.field.QM31.mul a31 b9
  let factors9 := index_mut_back8 a30
  let (a32, index_mut_back9) ← Array.index_mut_usize factors9 1#usize
  let a33 ←
    Array.update a32 4#usize (Array.make 4#usize [ q58, q59, q60, q61 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q61 _
  let factors9 := index_mut_back8 a30
  change ((do
  let (a32, index_mut_back9) ← Array.index_mut_usize factors9 1#usize
  let a33 ←
    Array.update a32 4#usize (Array.make 4#usize [ q58, q59, q60, q61 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back9 a33)
) >>= k) = (do
  let (a32, index_mut_back9) ← Array.index_mut_usize factors9 1#usize
  let a33 ←
    Array.update a32 4#usize (Array.make 4#usize [ q58, q59, q60, q61 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a32, index_mut_back9⟩ _
  change ((do
  let a33 ←
    Array.update a32 4#usize (Array.make 4#usize [ q58, q59, q60, q61 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back9 a33)
) >>= k) = (do
  let a33 ←
    Array.update a32 4#usize (Array.make 4#usize [ q58, q59, q60, q61 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back9 a33)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a33 _
  exact bind_tc_ok _ _
#print axioms row1_cps
end PV_B2_C_ConstructorRows
