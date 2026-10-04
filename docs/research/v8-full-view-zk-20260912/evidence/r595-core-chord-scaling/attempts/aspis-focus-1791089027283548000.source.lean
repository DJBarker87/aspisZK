import AspisV8R19.R574SparseGCorePolynomial

set_option autoImplicit false
namespace AspisV8R19.R595CoreChordScaling

open AspisV8R19.R574SparseGCorePolynomial

variable {F : Type*} [Field F] [NeZero (2 : F)]

 theorem coreMap_chord_scale (half alpha a b c scale : F)
    (x : Fin 271 → F) (i : Fin 271) :
    coreMap half alpha (scale*a) (scale*b) (scale*c) x i =
      scale * coreMap half alpha a b c x i := by
  unfold coreMap
  rw [sourceChord_components half (weightedQ alpha x) (scale*a) (scale*b) (scale*c),
    sourceChord_components half (weightedQ alpha x) a b c]
  ring

theorem coreMatrix_chord_scale (half alpha a b c scale : F) :
    coreMatrix half alpha (scale*a) (scale*b) (scale*c) =
      scale • coreMatrix half alpha a b c := by
  ext i j
  rw [coreMatrix_apply, coreMatrix_apply, coreMap_chord_scale]
  rfl

theorem coreMatrix_det_chord_scale (half alpha a b c scale : F) :
    (coreMatrix half alpha (scale*a) (scale*b) (scale*c)).det =
      scale^271 * (coreMatrix half alpha a b c).det := by
  rw [coreMatrix_chord_scale, Matrix.det_smul]
  simp

theorem coreMatrix_det_ne_zero_iff_chord_scale (half alpha a b c scale : F)
    (hscale : scale ≠ 0) :
    (coreMatrix half alpha (scale*a) (scale*b) (scale*c)).det ≠ 0 ↔
      (coreMatrix half alpha a b c).det ≠ 0 := by
  rw [coreMatrix_det_chord_scale]
  simp [hscale]

#print axioms coreMap_chord_scale
#print axioms coreMatrix_chord_scale
#print axioms coreMatrix_det_chord_scale
#print axioms coreMatrix_det_ne_zero_iff_chord_scale

end AspisV8R19.R595CoreChordScaling
