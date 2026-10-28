import R1Z.PV_B2_C_ConstructorCut3
set_option autoImplicit false
namespace PV_B2_C_ConstructorCuts
open Aeneas Aeneas.Std Result PV_B2_C_ArrayTotal
open PV_B2_C_WeightsNative PV_B2_C_ConstructorRows
def flat2 (variant : transport.Variant) (points : Points) (q q1 : K) (z : Array Point 2#usize) (prevBack : FactorRow → Factors) (prevRow : FactorRow) : Result (core.result.Result host_weights.Weights verifier.Error) := do
  let a34 ← Array.index_usize points 2#usize
  let a35 ← Array.index_usize a34 3#usize
  let b10 ← Array.index_usize a34 2#usize
  let q62 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a35
  let q63 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b10
  let q64 ← aspis_core.field.QM31.mul q62 q63
  let q65 ← aspis_core.field.QM31.mul a35 q63
  let q66 ← aspis_core.field.QM31.mul q62 b10
  let q67 ← aspis_core.field.QM31.mul a35 b10
  let factors10 := prevBack prevRow
  let (a36, index_mut_back10) ← Array.index_mut_usize factors10 2#usize
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
  let scp ← Array.index_usize z 0#usize
  let q92 ← aspis_core.field.QM31.mul scp.x scp.y
  let factors15 := index_mut_back14 a49
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
def cut2 (variant : transport.Variant) (points : Points) (q q1 : K) (z : Array Point 2#usize) (prevBack : FactorRow → Factors) (prevRow : FactorRow) : Result (core.result.Result host_weights.Weights verifier.Error) := do
  let a34 ← Array.index_usize points 2#usize
  let a35 ← Array.index_usize a34 3#usize
  let b10 ← Array.index_usize a34 2#usize
  let q62 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE a35
  let q63 ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE b10
  let q64 ← aspis_core.field.QM31.mul q62 q63
  let q65 ← aspis_core.field.QM31.mul a35 q63
  let q66 ← aspis_core.field.QM31.mul q62 b10
  let q67 ← aspis_core.field.QM31.mul a35 b10
  let factors10 := prevBack prevRow
  let (a36, index_mut_back10) ← Array.index_mut_usize factors10 2#usize
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
  flat3 variant points q q1 z index_mut_back14 a49

/-- Only one fixed-row prefix is compared; the remaining flat suffix is identical. -/
theorem flat2_eq_cut2 (variant : transport.Variant) (points : Points) (q q1 : K) (z : Array Point 2#usize) (prevBack : FactorRow → Factors) (prevRow : FactorRow) : flat2 variant points q q1 z prevBack prevRow = cut2 variant points q q1 z prevBack prevRow := by
  rfl

theorem cut2_total (variant : transport.Variant) (points : Points) (q q1 : K) (z : Array Point 2#usize) (prevBack : FactorRow → Factors) (prevRow : FactorRow) : RustOk (cut2 variant points q q1 z prevBack prevRow) := by
  unfold cut2
  apply bind_rust _ _ (read _ _ (by decide))
  intro a34
  apply bind_rust _ _ (read _ _ (by decide))
  intro a35
  apply bind_rust _ _ (read _ _ (by decide))
  intro b10
  apply bind_rust _ _ (⟨_,PV_B2_C_FieldTotal.QM31_sub _ _⟩)
  intro q62
  apply bind_rust _ _ (⟨_,PV_B2_C_FieldTotal.QM31_sub _ _⟩)
  intro q63
  apply bind_rust _ _ (⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩)
  intro q64
  apply bind_rust _ _ (⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩)
  intro q65
  apply bind_rust _ _ (⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩)
  intro q66
  apply bind_rust _ _ (⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩)
  intro q67
  apply bind_rust _ _ (borrow _ _ (by decide))
  rintro ⟨a36, index_mut_back10⟩
  apply bind_rust _ _ (write _ _ _ (by decide))
  intro a37
  apply bind_rust _ _ (read _ _ (by decide))
  intro a38
  apply bind_rust _ _ (read _ _ (by decide))
  intro b11
  apply bind_rust _ _ (⟨_,PV_B2_C_FieldTotal.QM31_sub _ _⟩)
  intro q68
  apply bind_rust _ _ (⟨_,PV_B2_C_FieldTotal.QM31_sub _ _⟩)
  intro q69
  apply bind_rust _ _ (⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩)
  intro q70
  apply bind_rust _ _ (⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩)
  intro q71
  apply bind_rust _ _ (⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩)
  intro q72
  apply bind_rust _ _ (⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩)
  intro q73
  apply bind_rust _ _ (borrow _ _ (by decide))
  rintro ⟨a39, index_mut_back11⟩
  apply bind_rust _ _ (write _ _ _ (by decide))
  intro a40
  apply bind_rust _ _ (read _ _ (by decide))
  intro a41
  apply bind_rust _ _ (read _ _ (by decide))
  intro b12
  apply bind_rust _ _ (⟨_,PV_B2_C_FieldTotal.QM31_sub _ _⟩)
  intro q74
  apply bind_rust _ _ (⟨_,PV_B2_C_FieldTotal.QM31_sub _ _⟩)
  intro q75
  apply bind_rust _ _ (⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩)
  intro q76
  apply bind_rust _ _ (⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩)
  intro q77
  apply bind_rust _ _ (⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩)
  intro q78
  apply bind_rust _ _ (⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩)
  intro q79
  apply bind_rust _ _ (borrow _ _ (by decide))
  rintro ⟨a42, index_mut_back12⟩
  apply bind_rust _ _ (write _ _ _ (by decide))
  intro a43
  apply bind_rust _ _ (read _ _ (by decide))
  intro a44
  apply bind_rust _ _ (read _ _ (by decide))
  intro b13
  apply bind_rust _ _ (⟨_,PV_B2_C_FieldTotal.QM31_sub _ _⟩)
  intro q80
  apply bind_rust _ _ (⟨_,PV_B2_C_FieldTotal.QM31_sub _ _⟩)
  intro q81
  apply bind_rust _ _ (⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩)
  intro q82
  apply bind_rust _ _ (⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩)
  intro q83
  apply bind_rust _ _ (⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩)
  intro q84
  apply bind_rust _ _ (⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩)
  intro q85
  apply bind_rust _ _ (borrow _ _ (by decide))
  rintro ⟨a45, index_mut_back13⟩
  apply bind_rust _ _ (write _ _ _ (by decide))
  intro a46
  apply bind_rust _ _ (read _ _ (by decide))
  intro a47
  apply bind_rust _ _ (read _ _ (by decide))
  intro b14
  apply bind_rust _ _ (⟨_,PV_B2_C_FieldTotal.QM31_sub _ _⟩)
  intro q86
  apply bind_rust _ _ (⟨_,PV_B2_C_FieldTotal.QM31_sub _ _⟩)
  intro q87
  apply bind_rust _ _ (⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩)
  intro q88
  apply bind_rust _ _ (⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩)
  intro q89
  apply bind_rust _ _ (⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩)
  intro q90
  apply bind_rust _ _ (⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩)
  intro q91
  apply bind_rust _ _ (borrow _ _ (by decide))
  rintro ⟨a48, index_mut_back14⟩
  apply bind_rust _ _ (write _ _ _ (by decide))
  intro a49
  exact flat3_total variant points q q1 z _ _

theorem flat2_total (variant : transport.Variant) (points : Points) (q q1 : K) (z : Array Point 2#usize) (prevBack : FactorRow → Factors) (prevRow : FactorRow) : RustOk (flat2 variant points q q1 z prevBack prevRow) := by
  rw [flat2_eq_cut2]
  exact cut2_total variant points q q1 z prevBack prevRow
#print axioms flat2_eq_cut2
#print axioms cut2_total
#print axioms flat2_total
end PV_B2_C_ConstructorCuts
