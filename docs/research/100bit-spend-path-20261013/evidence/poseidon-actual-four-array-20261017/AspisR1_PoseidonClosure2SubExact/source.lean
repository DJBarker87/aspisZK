import AspisR1.PoseidonPreparedFieldArithmetic
import ExtractedMaskTowerAdd

set_option autoImplicit false
namespace AspisR1.PoseidonClosure2SubExact
open Aeneas.Std Result AspisR1SelectedMaskProbe
open AspisV8R15.ExactTowerBase

abbrev QM := field.QM31
abbrev QMExact := AspisV8R15.ExactTowerBase.QM31Exact
abbrev CanonicalQM := AspisR1.ExtractedMaskTowerAdd.CanonicalQM
abbrev Decode := AspisR1.ExtractedMaskQM31Exact.decode

theorem qm_sub_decode (x y : QM) (hx : CanonicalQM x) (hy : CanonicalQM y) :
    ∃ z : QM, field.QM31.sub x y = .ok z ∧ CanonicalQM z ∧
      Decode z = Decode x - Decode y := by
  obtain ⟨z0, hz0, hcan0, _, _⟩ :=
    AspisR1.ExtractedMaskTowerAdd.current_cm_sub_mod x.c0 y.c0 hx.1 hy.1
  obtain ⟨z1, hz1, hcan1, _, _⟩ :=
    AspisR1.ExtractedMaskTowerAdd.current_cm_sub_mod x.c1 y.c1 hx.2 hy.2
  obtain ⟨z0', hz0', hv0⟩ :=
    AspisR1.PoseidonPreparedFieldArithmetic.cm_sub_decode x.c0 y.c0 hx.1 hy.1
  obtain ⟨z1', hz1', hv1⟩ :=
    AspisR1.PoseidonPreparedFieldArithmetic.cm_sub_decode x.c1 y.c1 hx.2 hy.2
  have heq0 : z0' = z0 := Result.ok.inj (hz0'.symm.trans hz0)
  have heq1 : z1' = z1 := Result.ok.inj (hz1'.symm.trans hz1)
  have hv0' : AspisR1.PoseidonPreparedFieldArithmetic.decodeCM z0 =
      AspisR1.PoseidonPreparedFieldArithmetic.decodeCM x.c0 -
        AspisR1.PoseidonPreparedFieldArithmetic.decodeCM y.c0 := by
    simpa [heq0] using hv0
  have hv1' : AspisR1.PoseidonPreparedFieldArithmetic.decodeCM z1 =
      AspisR1.PoseidonPreparedFieldArithmetic.decodeCM x.c1 -
        AspisR1.PoseidonPreparedFieldArithmetic.decodeCM y.c1 := by
    simpa [heq1] using hv1
  refine ⟨⟨z0,z1⟩, ?_, ⟨hcan0,hcan1⟩, ?_⟩
  · simp only [field.QM31.sub, hz0, hz1, bind_tc_ok]
  · apply QuadraticAlgebra.ext
    · apply QuadraticAlgebra.ext
      · have h := congrArg QuadraticAlgebra.re hv0'
        rw [QuadraticAlgebra.re_sub] at h
        simp [AspisR1.PoseidonPreparedFieldArithmetic.decodeCM,
          AspisR1.PoseidonPreparedFieldArithmetic.decodeM] at h
        simpa [Decode, AspisR1.ExtractedMaskQM31Exact.decode,
          AspisR1.PoseidonPreparedFieldArithmetic.decodeCM,
          AspisR1.PoseidonPreparedFieldArithmetic.decodeM] using h
      · have h := congrArg QuadraticAlgebra.im hv0'
        rw [QuadraticAlgebra.im_sub] at h
        simp [AspisR1.PoseidonPreparedFieldArithmetic.decodeCM,
          AspisR1.PoseidonPreparedFieldArithmetic.decodeM] at h
        simpa [Decode, AspisR1.ExtractedMaskQM31Exact.decode,
          AspisR1.PoseidonPreparedFieldArithmetic.decodeCM,
          AspisR1.PoseidonPreparedFieldArithmetic.decodeM] using h
    · apply QuadraticAlgebra.ext
      · have h := congrArg QuadraticAlgebra.re hv1'
        rw [QuadraticAlgebra.re_sub] at h
        simp [AspisR1.PoseidonPreparedFieldArithmetic.decodeCM,
          AspisR1.PoseidonPreparedFieldArithmetic.decodeM] at h
        simpa [Decode, AspisR1.ExtractedMaskQM31Exact.decode,
          AspisR1.PoseidonPreparedFieldArithmetic.decodeCM,
          AspisR1.PoseidonPreparedFieldArithmetic.decodeM] using h
      · have h := congrArg QuadraticAlgebra.im hv1'
        rw [QuadraticAlgebra.im_sub] at h
        simp [AspisR1.PoseidonPreparedFieldArithmetic.decodeCM,
          AspisR1.PoseidonPreparedFieldArithmetic.decodeM] at h
        simpa [Decode, AspisR1.ExtractedMaskQM31Exact.decode,
          AspisR1.PoseidonPreparedFieldArithmetic.decodeCM,
          AspisR1.PoseidonPreparedFieldArithmetic.decodeM] using h

#print axioms qm_sub_decode
end AspisR1.PoseidonClosure2SubExact
