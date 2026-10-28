import R1Z.PV_RDB2C_PV_B2_C_Row1Cps
set_option autoImplicit false
namespace PV_B2_C_ConstructorRows
open Aeneas Aeneas.Std Result PV_B2_C_WeightsNative
/-- Fixed row 2: reassociation with an arbitrary Result continuation only. -/
theorem row2_cps {α : Type} (factors : Factors) (points : Points)
    (k : Factors → Result α) :
    (row2 factors points >>= k) = (do
  let a34 ← Array.index_usize points 2#usize
  let a35 ← Array.index_usize a34 3#usize
  let b10 ← Array.index_usize a34 2#usize
  let q62 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a35
  let q63 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b10
  let q64 ← aspis_core.field.QM31.mul q62 q63
  let q65 ← aspis_core.field.QM31.mul a35 q63
  let q66 ← aspis_core.field.QM31.mul q62 b10
  let q67 ← aspis_core.field.QM31.mul a35 b10
  let (a36, index_mut_back10) ← Array.index_mut_usize factors 2#usize
  let a37 ←
    Array.update a36 0#usize (Array.make 4#usize [ q64, q65, q66, q67 ] : Array
      aspis_core.field.QM31 4#usize)
  let a38 ← Array.index_usize a34 1#usize
  let b11 ← Array.index_usize a34 0#usize
  let q68 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a38
  let q69 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b11
  let q70 ← aspis_core.field.QM31.mul q68 q69
  let q71 ← aspis_core.field.QM31.mul a38 q69
  let q72 ← aspis_core.field.QM31.mul q68 b11
  let q73 ← aspis_core.field.QM31.mul a38 b11
  let factors11 := index_mut_back10 a37
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
) := by
  unfold row2
  change ((do
  let a34 ← Array.index_usize points 2#usize
  let a35 ← Array.index_usize a34 3#usize
  let b10 ← Array.index_usize a34 2#usize
  let q62 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a35
  let q63 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b10
  let q64 ← aspis_core.field.QM31.mul q62 q63
  let q65 ← aspis_core.field.QM31.mul a35 q63
  let q66 ← aspis_core.field.QM31.mul q62 b10
  let q67 ← aspis_core.field.QM31.mul a35 b10
  let (a36, index_mut_back10) ← Array.index_mut_usize factors 2#usize
  let a37 ←
    Array.update a36 0#usize (Array.make 4#usize [ q64, q65, q66, q67 ] : Array
      aspis_core.field.QM31 4#usize)
  let a38 ← Array.index_usize a34 1#usize
  let b11 ← Array.index_usize a34 0#usize
  let q68 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a38
  let q69 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b11
  let q70 ← aspis_core.field.QM31.mul q68 q69
  let q71 ← aspis_core.field.QM31.mul a38 q69
  let q72 ← aspis_core.field.QM31.mul q68 b11
  let q73 ← aspis_core.field.QM31.mul a38 b11
  let factors11 := index_mut_back10 a37
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let a34 ← Array.index_usize points 2#usize
  let a35 ← Array.index_usize a34 3#usize
  let b10 ← Array.index_usize a34 2#usize
  let q62 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a35
  let q63 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b10
  let q64 ← aspis_core.field.QM31.mul q62 q63
  let q65 ← aspis_core.field.QM31.mul a35 q63
  let q66 ← aspis_core.field.QM31.mul q62 b10
  let q67 ← aspis_core.field.QM31.mul a35 b10
  let (a36, index_mut_back10) ← Array.index_mut_usize factors 2#usize
  let a37 ←
    Array.update a36 0#usize (Array.make 4#usize [ q64, q65, q66, q67 ] : Array
      aspis_core.field.QM31 4#usize)
  let a38 ← Array.index_usize a34 1#usize
  let b11 ← Array.index_usize a34 0#usize
  let q68 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a38
  let q69 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b11
  let q70 ← aspis_core.field.QM31.mul q68 q69
  let q71 ← aspis_core.field.QM31.mul a38 q69
  let q72 ← aspis_core.field.QM31.mul q68 b11
  let q73 ← aspis_core.field.QM31.mul a38 b11
  let factors11 := index_mut_back10 a37
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a34 _
  change ((do
  let a35 ← Array.index_usize a34 3#usize
  let b10 ← Array.index_usize a34 2#usize
  let q62 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a35
  let q63 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b10
  let q64 ← aspis_core.field.QM31.mul q62 q63
  let q65 ← aspis_core.field.QM31.mul a35 q63
  let q66 ← aspis_core.field.QM31.mul q62 b10
  let q67 ← aspis_core.field.QM31.mul a35 b10
  let (a36, index_mut_back10) ← Array.index_mut_usize factors 2#usize
  let a37 ←
    Array.update a36 0#usize (Array.make 4#usize [ q64, q65, q66, q67 ] : Array
      aspis_core.field.QM31 4#usize)
  let a38 ← Array.index_usize a34 1#usize
  let b11 ← Array.index_usize a34 0#usize
  let q68 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a38
  let q69 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b11
  let q70 ← aspis_core.field.QM31.mul q68 q69
  let q71 ← aspis_core.field.QM31.mul a38 q69
  let q72 ← aspis_core.field.QM31.mul q68 b11
  let q73 ← aspis_core.field.QM31.mul a38 b11
  let factors11 := index_mut_back10 a37
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let a35 ← Array.index_usize a34 3#usize
  let b10 ← Array.index_usize a34 2#usize
  let q62 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a35
  let q63 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b10
  let q64 ← aspis_core.field.QM31.mul q62 q63
  let q65 ← aspis_core.field.QM31.mul a35 q63
  let q66 ← aspis_core.field.QM31.mul q62 b10
  let q67 ← aspis_core.field.QM31.mul a35 b10
  let (a36, index_mut_back10) ← Array.index_mut_usize factors 2#usize
  let a37 ←
    Array.update a36 0#usize (Array.make 4#usize [ q64, q65, q66, q67 ] : Array
      aspis_core.field.QM31 4#usize)
  let a38 ← Array.index_usize a34 1#usize
  let b11 ← Array.index_usize a34 0#usize
  let q68 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a38
  let q69 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b11
  let q70 ← aspis_core.field.QM31.mul q68 q69
  let q71 ← aspis_core.field.QM31.mul a38 q69
  let q72 ← aspis_core.field.QM31.mul q68 b11
  let q73 ← aspis_core.field.QM31.mul a38 b11
  let factors11 := index_mut_back10 a37
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a35 _
  change ((do
  let b10 ← Array.index_usize a34 2#usize
  let q62 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a35
  let q63 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b10
  let q64 ← aspis_core.field.QM31.mul q62 q63
  let q65 ← aspis_core.field.QM31.mul a35 q63
  let q66 ← aspis_core.field.QM31.mul q62 b10
  let q67 ← aspis_core.field.QM31.mul a35 b10
  let (a36, index_mut_back10) ← Array.index_mut_usize factors 2#usize
  let a37 ←
    Array.update a36 0#usize (Array.make 4#usize [ q64, q65, q66, q67 ] : Array
      aspis_core.field.QM31 4#usize)
  let a38 ← Array.index_usize a34 1#usize
  let b11 ← Array.index_usize a34 0#usize
  let q68 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a38
  let q69 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b11
  let q70 ← aspis_core.field.QM31.mul q68 q69
  let q71 ← aspis_core.field.QM31.mul a38 q69
  let q72 ← aspis_core.field.QM31.mul q68 b11
  let q73 ← aspis_core.field.QM31.mul a38 b11
  let factors11 := index_mut_back10 a37
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let b10 ← Array.index_usize a34 2#usize
  let q62 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a35
  let q63 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b10
  let q64 ← aspis_core.field.QM31.mul q62 q63
  let q65 ← aspis_core.field.QM31.mul a35 q63
  let q66 ← aspis_core.field.QM31.mul q62 b10
  let q67 ← aspis_core.field.QM31.mul a35 b10
  let (a36, index_mut_back10) ← Array.index_mut_usize factors 2#usize
  let a37 ←
    Array.update a36 0#usize (Array.make 4#usize [ q64, q65, q66, q67 ] : Array
      aspis_core.field.QM31 4#usize)
  let a38 ← Array.index_usize a34 1#usize
  let b11 ← Array.index_usize a34 0#usize
  let q68 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a38
  let q69 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b11
  let q70 ← aspis_core.field.QM31.mul q68 q69
  let q71 ← aspis_core.field.QM31.mul a38 q69
  let q72 ← aspis_core.field.QM31.mul q68 b11
  let q73 ← aspis_core.field.QM31.mul a38 b11
  let factors11 := index_mut_back10 a37
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro b10 _
  change ((do
  let q62 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a35
  let q63 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b10
  let q64 ← aspis_core.field.QM31.mul q62 q63
  let q65 ← aspis_core.field.QM31.mul a35 q63
  let q66 ← aspis_core.field.QM31.mul q62 b10
  let q67 ← aspis_core.field.QM31.mul a35 b10
  let (a36, index_mut_back10) ← Array.index_mut_usize factors 2#usize
  let a37 ←
    Array.update a36 0#usize (Array.make 4#usize [ q64, q65, q66, q67 ] : Array
      aspis_core.field.QM31 4#usize)
  let a38 ← Array.index_usize a34 1#usize
  let b11 ← Array.index_usize a34 0#usize
  let q68 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a38
  let q69 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b11
  let q70 ← aspis_core.field.QM31.mul q68 q69
  let q71 ← aspis_core.field.QM31.mul a38 q69
  let q72 ← aspis_core.field.QM31.mul q68 b11
  let q73 ← aspis_core.field.QM31.mul a38 b11
  let factors11 := index_mut_back10 a37
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let q62 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a35
  let q63 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b10
  let q64 ← aspis_core.field.QM31.mul q62 q63
  let q65 ← aspis_core.field.QM31.mul a35 q63
  let q66 ← aspis_core.field.QM31.mul q62 b10
  let q67 ← aspis_core.field.QM31.mul a35 b10
  let (a36, index_mut_back10) ← Array.index_mut_usize factors 2#usize
  let a37 ←
    Array.update a36 0#usize (Array.make 4#usize [ q64, q65, q66, q67 ] : Array
      aspis_core.field.QM31 4#usize)
  let a38 ← Array.index_usize a34 1#usize
  let b11 ← Array.index_usize a34 0#usize
  let q68 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a38
  let q69 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b11
  let q70 ← aspis_core.field.QM31.mul q68 q69
  let q71 ← aspis_core.field.QM31.mul a38 q69
  let q72 ← aspis_core.field.QM31.mul q68 b11
  let q73 ← aspis_core.field.QM31.mul a38 b11
  let factors11 := index_mut_back10 a37
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q62 _
  change ((do
  let q63 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b10
  let q64 ← aspis_core.field.QM31.mul q62 q63
  let q65 ← aspis_core.field.QM31.mul a35 q63
  let q66 ← aspis_core.field.QM31.mul q62 b10
  let q67 ← aspis_core.field.QM31.mul a35 b10
  let (a36, index_mut_back10) ← Array.index_mut_usize factors 2#usize
  let a37 ←
    Array.update a36 0#usize (Array.make 4#usize [ q64, q65, q66, q67 ] : Array
      aspis_core.field.QM31 4#usize)
  let a38 ← Array.index_usize a34 1#usize
  let b11 ← Array.index_usize a34 0#usize
  let q68 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a38
  let q69 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b11
  let q70 ← aspis_core.field.QM31.mul q68 q69
  let q71 ← aspis_core.field.QM31.mul a38 q69
  let q72 ← aspis_core.field.QM31.mul q68 b11
  let q73 ← aspis_core.field.QM31.mul a38 b11
  let factors11 := index_mut_back10 a37
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let q63 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b10
  let q64 ← aspis_core.field.QM31.mul q62 q63
  let q65 ← aspis_core.field.QM31.mul a35 q63
  let q66 ← aspis_core.field.QM31.mul q62 b10
  let q67 ← aspis_core.field.QM31.mul a35 b10
  let (a36, index_mut_back10) ← Array.index_mut_usize factors 2#usize
  let a37 ←
    Array.update a36 0#usize (Array.make 4#usize [ q64, q65, q66, q67 ] : Array
      aspis_core.field.QM31 4#usize)
  let a38 ← Array.index_usize a34 1#usize
  let b11 ← Array.index_usize a34 0#usize
  let q68 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a38
  let q69 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b11
  let q70 ← aspis_core.field.QM31.mul q68 q69
  let q71 ← aspis_core.field.QM31.mul a38 q69
  let q72 ← aspis_core.field.QM31.mul q68 b11
  let q73 ← aspis_core.field.QM31.mul a38 b11
  let factors11 := index_mut_back10 a37
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q63 _
  change ((do
  let q64 ← aspis_core.field.QM31.mul q62 q63
  let q65 ← aspis_core.field.QM31.mul a35 q63
  let q66 ← aspis_core.field.QM31.mul q62 b10
  let q67 ← aspis_core.field.QM31.mul a35 b10
  let (a36, index_mut_back10) ← Array.index_mut_usize factors 2#usize
  let a37 ←
    Array.update a36 0#usize (Array.make 4#usize [ q64, q65, q66, q67 ] : Array
      aspis_core.field.QM31 4#usize)
  let a38 ← Array.index_usize a34 1#usize
  let b11 ← Array.index_usize a34 0#usize
  let q68 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a38
  let q69 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b11
  let q70 ← aspis_core.field.QM31.mul q68 q69
  let q71 ← aspis_core.field.QM31.mul a38 q69
  let q72 ← aspis_core.field.QM31.mul q68 b11
  let q73 ← aspis_core.field.QM31.mul a38 b11
  let factors11 := index_mut_back10 a37
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let q64 ← aspis_core.field.QM31.mul q62 q63
  let q65 ← aspis_core.field.QM31.mul a35 q63
  let q66 ← aspis_core.field.QM31.mul q62 b10
  let q67 ← aspis_core.field.QM31.mul a35 b10
  let (a36, index_mut_back10) ← Array.index_mut_usize factors 2#usize
  let a37 ←
    Array.update a36 0#usize (Array.make 4#usize [ q64, q65, q66, q67 ] : Array
      aspis_core.field.QM31 4#usize)
  let a38 ← Array.index_usize a34 1#usize
  let b11 ← Array.index_usize a34 0#usize
  let q68 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a38
  let q69 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b11
  let q70 ← aspis_core.field.QM31.mul q68 q69
  let q71 ← aspis_core.field.QM31.mul a38 q69
  let q72 ← aspis_core.field.QM31.mul q68 b11
  let q73 ← aspis_core.field.QM31.mul a38 b11
  let factors11 := index_mut_back10 a37
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q64 _
  change ((do
  let q65 ← aspis_core.field.QM31.mul a35 q63
  let q66 ← aspis_core.field.QM31.mul q62 b10
  let q67 ← aspis_core.field.QM31.mul a35 b10
  let (a36, index_mut_back10) ← Array.index_mut_usize factors 2#usize
  let a37 ←
    Array.update a36 0#usize (Array.make 4#usize [ q64, q65, q66, q67 ] : Array
      aspis_core.field.QM31 4#usize)
  let a38 ← Array.index_usize a34 1#usize
  let b11 ← Array.index_usize a34 0#usize
  let q68 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a38
  let q69 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b11
  let q70 ← aspis_core.field.QM31.mul q68 q69
  let q71 ← aspis_core.field.QM31.mul a38 q69
  let q72 ← aspis_core.field.QM31.mul q68 b11
  let q73 ← aspis_core.field.QM31.mul a38 b11
  let factors11 := index_mut_back10 a37
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let q65 ← aspis_core.field.QM31.mul a35 q63
  let q66 ← aspis_core.field.QM31.mul q62 b10
  let q67 ← aspis_core.field.QM31.mul a35 b10
  let (a36, index_mut_back10) ← Array.index_mut_usize factors 2#usize
  let a37 ←
    Array.update a36 0#usize (Array.make 4#usize [ q64, q65, q66, q67 ] : Array
      aspis_core.field.QM31 4#usize)
  let a38 ← Array.index_usize a34 1#usize
  let b11 ← Array.index_usize a34 0#usize
  let q68 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a38
  let q69 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b11
  let q70 ← aspis_core.field.QM31.mul q68 q69
  let q71 ← aspis_core.field.QM31.mul a38 q69
  let q72 ← aspis_core.field.QM31.mul q68 b11
  let q73 ← aspis_core.field.QM31.mul a38 b11
  let factors11 := index_mut_back10 a37
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q65 _
  change ((do
  let q66 ← aspis_core.field.QM31.mul q62 b10
  let q67 ← aspis_core.field.QM31.mul a35 b10
  let (a36, index_mut_back10) ← Array.index_mut_usize factors 2#usize
  let a37 ←
    Array.update a36 0#usize (Array.make 4#usize [ q64, q65, q66, q67 ] : Array
      aspis_core.field.QM31 4#usize)
  let a38 ← Array.index_usize a34 1#usize
  let b11 ← Array.index_usize a34 0#usize
  let q68 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a38
  let q69 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b11
  let q70 ← aspis_core.field.QM31.mul q68 q69
  let q71 ← aspis_core.field.QM31.mul a38 q69
  let q72 ← aspis_core.field.QM31.mul q68 b11
  let q73 ← aspis_core.field.QM31.mul a38 b11
  let factors11 := index_mut_back10 a37
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let q66 ← aspis_core.field.QM31.mul q62 b10
  let q67 ← aspis_core.field.QM31.mul a35 b10
  let (a36, index_mut_back10) ← Array.index_mut_usize factors 2#usize
  let a37 ←
    Array.update a36 0#usize (Array.make 4#usize [ q64, q65, q66, q67 ] : Array
      aspis_core.field.QM31 4#usize)
  let a38 ← Array.index_usize a34 1#usize
  let b11 ← Array.index_usize a34 0#usize
  let q68 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a38
  let q69 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b11
  let q70 ← aspis_core.field.QM31.mul q68 q69
  let q71 ← aspis_core.field.QM31.mul a38 q69
  let q72 ← aspis_core.field.QM31.mul q68 b11
  let q73 ← aspis_core.field.QM31.mul a38 b11
  let factors11 := index_mut_back10 a37
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q66 _
  change ((do
  let q67 ← aspis_core.field.QM31.mul a35 b10
  let (a36, index_mut_back10) ← Array.index_mut_usize factors 2#usize
  let a37 ←
    Array.update a36 0#usize (Array.make 4#usize [ q64, q65, q66, q67 ] : Array
      aspis_core.field.QM31 4#usize)
  let a38 ← Array.index_usize a34 1#usize
  let b11 ← Array.index_usize a34 0#usize
  let q68 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a38
  let q69 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b11
  let q70 ← aspis_core.field.QM31.mul q68 q69
  let q71 ← aspis_core.field.QM31.mul a38 q69
  let q72 ← aspis_core.field.QM31.mul q68 b11
  let q73 ← aspis_core.field.QM31.mul a38 b11
  let factors11 := index_mut_back10 a37
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let q67 ← aspis_core.field.QM31.mul a35 b10
  let (a36, index_mut_back10) ← Array.index_mut_usize factors 2#usize
  let a37 ←
    Array.update a36 0#usize (Array.make 4#usize [ q64, q65, q66, q67 ] : Array
      aspis_core.field.QM31 4#usize)
  let a38 ← Array.index_usize a34 1#usize
  let b11 ← Array.index_usize a34 0#usize
  let q68 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a38
  let q69 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b11
  let q70 ← aspis_core.field.QM31.mul q68 q69
  let q71 ← aspis_core.field.QM31.mul a38 q69
  let q72 ← aspis_core.field.QM31.mul q68 b11
  let q73 ← aspis_core.field.QM31.mul a38 b11
  let factors11 := index_mut_back10 a37
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q67 _
  change ((do
  let (a36, index_mut_back10) ← Array.index_mut_usize factors 2#usize
  let a37 ←
    Array.update a36 0#usize (Array.make 4#usize [ q64, q65, q66, q67 ] : Array
      aspis_core.field.QM31 4#usize)
  let a38 ← Array.index_usize a34 1#usize
  let b11 ← Array.index_usize a34 0#usize
  let q68 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a38
  let q69 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b11
  let q70 ← aspis_core.field.QM31.mul q68 q69
  let q71 ← aspis_core.field.QM31.mul a38 q69
  let q72 ← aspis_core.field.QM31.mul q68 b11
  let q73 ← aspis_core.field.QM31.mul a38 b11
  let factors11 := index_mut_back10 a37
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let (a36, index_mut_back10) ← Array.index_mut_usize factors 2#usize
  let a37 ←
    Array.update a36 0#usize (Array.make 4#usize [ q64, q65, q66, q67 ] : Array
      aspis_core.field.QM31 4#usize)
  let a38 ← Array.index_usize a34 1#usize
  let b11 ← Array.index_usize a34 0#usize
  let q68 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a38
  let q69 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b11
  let q70 ← aspis_core.field.QM31.mul q68 q69
  let q71 ← aspis_core.field.QM31.mul a38 q69
  let q72 ← aspis_core.field.QM31.mul q68 b11
  let q73 ← aspis_core.field.QM31.mul a38 b11
  let factors11 := index_mut_back10 a37
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a36, index_mut_back10⟩ _
  change ((do
  let a37 ←
    Array.update a36 0#usize (Array.make 4#usize [ q64, q65, q66, q67 ] : Array
      aspis_core.field.QM31 4#usize)
  let a38 ← Array.index_usize a34 1#usize
  let b11 ← Array.index_usize a34 0#usize
  let q68 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a38
  let q69 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b11
  let q70 ← aspis_core.field.QM31.mul q68 q69
  let q71 ← aspis_core.field.QM31.mul a38 q69
  let q72 ← aspis_core.field.QM31.mul q68 b11
  let q73 ← aspis_core.field.QM31.mul a38 b11
  let factors11 := index_mut_back10 a37
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let a37 ←
    Array.update a36 0#usize (Array.make 4#usize [ q64, q65, q66, q67 ] : Array
      aspis_core.field.QM31 4#usize)
  let a38 ← Array.index_usize a34 1#usize
  let b11 ← Array.index_usize a34 0#usize
  let q68 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a38
  let q69 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b11
  let q70 ← aspis_core.field.QM31.mul q68 q69
  let q71 ← aspis_core.field.QM31.mul a38 q69
  let q72 ← aspis_core.field.QM31.mul q68 b11
  let q73 ← aspis_core.field.QM31.mul a38 b11
  let factors11 := index_mut_back10 a37
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a37 _
  change ((do
  let a38 ← Array.index_usize a34 1#usize
  let b11 ← Array.index_usize a34 0#usize
  let q68 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a38
  let q69 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b11
  let q70 ← aspis_core.field.QM31.mul q68 q69
  let q71 ← aspis_core.field.QM31.mul a38 q69
  let q72 ← aspis_core.field.QM31.mul q68 b11
  let q73 ← aspis_core.field.QM31.mul a38 b11
  let factors11 := index_mut_back10 a37
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let a38 ← Array.index_usize a34 1#usize
  let b11 ← Array.index_usize a34 0#usize
  let q68 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a38
  let q69 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b11
  let q70 ← aspis_core.field.QM31.mul q68 q69
  let q71 ← aspis_core.field.QM31.mul a38 q69
  let q72 ← aspis_core.field.QM31.mul q68 b11
  let q73 ← aspis_core.field.QM31.mul a38 b11
  let factors11 := index_mut_back10 a37
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a38 _
  change ((do
  let b11 ← Array.index_usize a34 0#usize
  let q68 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a38
  let q69 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b11
  let q70 ← aspis_core.field.QM31.mul q68 q69
  let q71 ← aspis_core.field.QM31.mul a38 q69
  let q72 ← aspis_core.field.QM31.mul q68 b11
  let q73 ← aspis_core.field.QM31.mul a38 b11
  let factors11 := index_mut_back10 a37
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let b11 ← Array.index_usize a34 0#usize
  let q68 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a38
  let q69 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b11
  let q70 ← aspis_core.field.QM31.mul q68 q69
  let q71 ← aspis_core.field.QM31.mul a38 q69
  let q72 ← aspis_core.field.QM31.mul q68 b11
  let q73 ← aspis_core.field.QM31.mul a38 b11
  let factors11 := index_mut_back10 a37
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro b11 _
  change ((do
  let q68 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a38
  let q69 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b11
  let q70 ← aspis_core.field.QM31.mul q68 q69
  let q71 ← aspis_core.field.QM31.mul a38 q69
  let q72 ← aspis_core.field.QM31.mul q68 b11
  let q73 ← aspis_core.field.QM31.mul a38 b11
  let factors11 := index_mut_back10 a37
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let q68 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a38
  let q69 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b11
  let q70 ← aspis_core.field.QM31.mul q68 q69
  let q71 ← aspis_core.field.QM31.mul a38 q69
  let q72 ← aspis_core.field.QM31.mul q68 b11
  let q73 ← aspis_core.field.QM31.mul a38 b11
  let factors11 := index_mut_back10 a37
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q68 _
  change ((do
  let q69 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b11
  let q70 ← aspis_core.field.QM31.mul q68 q69
  let q71 ← aspis_core.field.QM31.mul a38 q69
  let q72 ← aspis_core.field.QM31.mul q68 b11
  let q73 ← aspis_core.field.QM31.mul a38 b11
  let factors11 := index_mut_back10 a37
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let q69 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b11
  let q70 ← aspis_core.field.QM31.mul q68 q69
  let q71 ← aspis_core.field.QM31.mul a38 q69
  let q72 ← aspis_core.field.QM31.mul q68 b11
  let q73 ← aspis_core.field.QM31.mul a38 b11
  let factors11 := index_mut_back10 a37
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q69 _
  change ((do
  let q70 ← aspis_core.field.QM31.mul q68 q69
  let q71 ← aspis_core.field.QM31.mul a38 q69
  let q72 ← aspis_core.field.QM31.mul q68 b11
  let q73 ← aspis_core.field.QM31.mul a38 b11
  let factors11 := index_mut_back10 a37
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let q70 ← aspis_core.field.QM31.mul q68 q69
  let q71 ← aspis_core.field.QM31.mul a38 q69
  let q72 ← aspis_core.field.QM31.mul q68 b11
  let q73 ← aspis_core.field.QM31.mul a38 b11
  let factors11 := index_mut_back10 a37
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q70 _
  change ((do
  let q71 ← aspis_core.field.QM31.mul a38 q69
  let q72 ← aspis_core.field.QM31.mul q68 b11
  let q73 ← aspis_core.field.QM31.mul a38 b11
  let factors11 := index_mut_back10 a37
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let q71 ← aspis_core.field.QM31.mul a38 q69
  let q72 ← aspis_core.field.QM31.mul q68 b11
  let q73 ← aspis_core.field.QM31.mul a38 b11
  let factors11 := index_mut_back10 a37
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q71 _
  change ((do
  let q72 ← aspis_core.field.QM31.mul q68 b11
  let q73 ← aspis_core.field.QM31.mul a38 b11
  let factors11 := index_mut_back10 a37
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let q72 ← aspis_core.field.QM31.mul q68 b11
  let q73 ← aspis_core.field.QM31.mul a38 b11
  let factors11 := index_mut_back10 a37
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q72 _
  change ((do
  let q73 ← aspis_core.field.QM31.mul a38 b11
  let factors11 := index_mut_back10 a37
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let q73 ← aspis_core.field.QM31.mul a38 b11
  let factors11 := index_mut_back10 a37
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q73 _
  let factors11 := index_mut_back10 a37
  change ((do
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let (a39, index_mut_back11) ← Array.index_mut_usize factors11 2#usize
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a39, index_mut_back11⟩ _
  change ((do
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let a40 ←
    Array.update a39 1#usize (Array.make 4#usize [ q70, q71, q72, q73 ] : Array
      aspis_core.field.QM31 4#usize)
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a40 _
  change ((do
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let a41 ← Array.index_usize a34 5#usize
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a41 _
  change ((do
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let b12 ← Array.index_usize a34 4#usize
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro b12 _
  change ((do
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let q74 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a41
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q74 _
  change ((do
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let q75 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b12
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q75 _
  change ((do
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let q76 ← aspis_core.field.QM31.mul q74 q75
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q76 _
  change ((do
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let q77 ← aspis_core.field.QM31.mul a41 q75
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q77 _
  change ((do
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let q78 ← aspis_core.field.QM31.mul q74 b12
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q78 _
  change ((do
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let q79 ← aspis_core.field.QM31.mul a41 b12
  let factors12 := index_mut_back11 a40
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q79 _
  let factors12 := index_mut_back11 a40
  change ((do
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let (a42, index_mut_back12) ← Array.index_mut_usize factors12 2#usize
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a42, index_mut_back12⟩ _
  change ((do
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let a43 ←
    Array.update a42 2#usize (Array.make 4#usize [ q76, q77, q78, q79 ] : Array
      aspis_core.field.QM31 4#usize)
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a43 _
  change ((do
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let a44 ← Array.index_usize a34 9#usize
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a44 _
  change ((do
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let b13 ← Array.index_usize a34 8#usize
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro b13 _
  change ((do
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let q80 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a44
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q80 _
  change ((do
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let q81 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b13
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q81 _
  change ((do
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let q82 ← aspis_core.field.QM31.mul q80 q81
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q82 _
  change ((do
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let q83 ← aspis_core.field.QM31.mul a44 q81
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q83 _
  change ((do
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let q84 ← aspis_core.field.QM31.mul q80 b13
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q84 _
  change ((do
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let q85 ← aspis_core.field.QM31.mul a44 b13
  let factors13 := index_mut_back12 a43
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q85 _
  let factors13 := index_mut_back12 a43
  change ((do
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let (a45, index_mut_back13) ← Array.index_mut_usize factors13 2#usize
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a45, index_mut_back13⟩ _
  change ((do
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let a46 ←
    Array.update a45 3#usize (Array.make 4#usize [ q82, q83, q84, q85 ] : Array
      aspis_core.field.QM31 4#usize)
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a46 _
  change ((do
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let a47 ← Array.index_usize a34 7#usize
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a47 _
  change ((do
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let b14 ← Array.index_usize a34 6#usize
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro b14 _
  change ((do
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let q86 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a47
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q86 _
  change ((do
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let q87 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b14
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q87 _
  change ((do
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let q88 ← aspis_core.field.QM31.mul q86 q87
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q88 _
  change ((do
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let q89 ← aspis_core.field.QM31.mul a47 q87
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q89 _
  change ((do
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let q90 ← aspis_core.field.QM31.mul q86 b14
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q90 _
  change ((do
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let q91 ← aspis_core.field.QM31.mul a47 b14
  let factors14 := index_mut_back13 a46
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro q91 _
  let factors14 := index_mut_back13 a46
  change ((do
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let (a48, index_mut_back14) ← Array.index_mut_usize factors14 2#usize
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a48, index_mut_back14⟩ _
  change ((do
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  ok (index_mut_back14 a49)
) >>= k) = (do
  let a49 ←
    Array.update a48 4#usize (Array.make 4#usize [ q88, q89, q90, q91 ] : Array
      aspis_core.field.QM31 4#usize)
  k (index_mut_back14 a49)
)
  rw [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro a49 _
  exact bind_tc_ok _ _
#print axioms row2_cps
end PV_B2_C_ConstructorRows
