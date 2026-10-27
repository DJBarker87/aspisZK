import ExtractedMaskM31AddSub
import ExtractedMaskTowerAdd
import ExtractedMaskQM31Exact
import RPu_AspisR1.PoseidonPreparedKaratsubaSuccess

set_option autoImplicit false
namespace AspisR1.PoseidonPreparedFieldArithmetic
open Aeneas.Std Result AspisR1SelectedMaskProbe
open AspisV8R15.ExactTowerBase

abbrev P : Nat := 2147483647
abbrev M := AspisV8R15.ExactTowerBase.M31Exact
abbrev CMExact := AspisV8R15.ExactTowerBase.CM31Exact
abbrev M31 := field.M31
abbrev CM := field.CM31
abbrev CanonicalCM := AspisR1.ExtractedMaskTowerAdd.CanonicalCM

def decodeM (x : M31) : M := x.val
def decodeCM (x : CM) : CMExact := ⟨decodeM x.a, decodeM x.b⟩

private theorem cast_mod (n : Nat) : ((n % P : Nat) : M) = (n : M) := by
  simp only [ZMod.natCast_mod]

private theorem cast_sub_wrap (a b : Nat) (hb : b < P) :
    (((a + P - b) % P : Nat) : M) = (a : M) - (b : M) := by
  rw [ZMod.natCast_mod, Nat.cast_sub (by omega), Nat.cast_add,
    ZMod.natCast_self, add_zero]

theorem m31_add_decode (x y : M31) (hx : x.val < P) (hy : y.val < P) :
    ∃ z, field.M31.add x y = .ok z ∧ decodeM z = decodeM x + decodeM y := by
  obtain ⟨z, hz, hv, _⟩ := AspisR1.ExtractedMaskM31AddSub.current_add_mod x y hx hy
  refine ⟨z, hz, ?_⟩
  change (z.val : M) = (x.val : M) + (y.val : M)
  rw [hv, cast_mod]
  simp [decodeM]

theorem m31_sub_decode (x y : M31) (hx : x.val < P) (hy : y.val < P) :
    ∃ z, field.M31.sub x y = .ok z ∧ decodeM z = decodeM x - decodeM y := by
  obtain ⟨z, hz, hv, _⟩ := AspisR1.ExtractedMaskM31AddSub.current_sub_mod x y hx hy
  refine ⟨z, hz, ?_⟩
  change (z.val : M) = (x.val : M) - (y.val : M)
  rw [hv]
  exact cast_sub_wrap x.val y.val hy

theorem cm_add_decode (x y : CM) (hx : CanonicalCM x) (hy : CanonicalCM y) :
    ∃ z, field.CM31.add x y = .ok z ∧ decodeCM z = decodeCM x + decodeCM y := by
  obtain ⟨z, hz, _, ha, hb⟩ := AspisR1.ExtractedMaskTowerAdd.current_cm_add_mod x y hx hy
  refine ⟨z, hz, ?_⟩
  apply QuadraticAlgebra.ext <;> simp [decodeCM, decodeM, ha, hb, cast_mod]

theorem cm_sub_decode (x y : CM) (hx : CanonicalCM x) (hy : CanonicalCM y) :
    ∃ z, field.CM31.sub x y = .ok z ∧ decodeCM z = decodeCM x - decodeCM y := by
  obtain ⟨z, hz, _, ha, hb⟩ := AspisR1.ExtractedMaskTowerAdd.current_cm_sub_mod x y hx hy
  refine ⟨z, hz, ?_⟩
  apply QuadraticAlgebra.ext
  · change (z.a.val : M) = (x.a.val : M) - (y.a.val : M)
    rw [ha, ZMod.natCast_mod]
    have h := cast_sub_wrap x.a.val y.a.val hy.1
    simpa [P, AspisR1.ExtractedMaskTowerAdd.P] using h
  · change (z.b.val : M) = (x.b.val : M) - (y.b.val : M)
    rw [hb, ZMod.natCast_mod]
    have h := cast_sub_wrap x.b.val y.b.val hy.2
    simpa [P, AspisR1.ExtractedMaskTowerAdd.P] using h

theorem mul_by_r_decode (x : CM) (hx : CanonicalCM x) :
    ∃ y, field.mul_by_r x = .ok y ∧ CanonicalCM y ∧
      decodeCM y = ⟨2, 1⟩ * decodeCM x := by
  obtain ⟨a2, ea2, hva2, ca2⟩ := AspisR1.ExtractedMaskM31AddSub.current_add_mod x.a x.a hx.1 hx.1
  obtain ⟨a, ea, hva, ca⟩ := AspisR1.ExtractedMaskM31AddSub.current_sub_mod a2 x.b ca2 hx.2
  obtain ⟨b2, eb2, hvb2, cb2⟩ := AspisR1.ExtractedMaskM31AddSub.current_add_mod x.b x.b hx.2 hx.2
  obtain ⟨b, eb, hvb, cb⟩ := AspisR1.ExtractedMaskM31AddSub.current_add_mod x.a b2 hx.1 cb2
  have hda2 : decodeM a2 = decodeM x.a + decodeM x.a := by
    change (a2.val : M) = (x.a.val : M) + (x.a.val : M)
    rw [hva2, cast_mod]
    simp [decodeM]
  have hda : decodeM a = decodeM a2 - decodeM x.b := by
    change (a.val : M) = (a2.val : M) - (x.b.val : M)
    rw [hva]
    exact cast_sub_wrap a2.val x.b.val hx.2
  have hdb2 : decodeM b2 = decodeM x.b + decodeM x.b := by
    change (b2.val : M) = (x.b.val : M) + (x.b.val : M)
    rw [hvb2, cast_mod]
    simp [decodeM]
  have hdb : decodeM b = decodeM x.a + decodeM b2 := by
    change (b.val : M) = (x.a.val : M) + (b2.val : M)
    rw [hvb, cast_mod]
    simp [decodeM]
  refine ⟨⟨a, b⟩, ?_, ⟨ca, cb⟩, ?_⟩
  · simp only [field.mul_by_r, field.M31.double, ea2, ea, eb2, eb, bind_tc_ok]
  · apply QuadraticAlgebra.ext
    · change decodeM a = _
      rw [hda, hda2]
      simp [QuadraticAlgebra.re_mul, decodeCM, qm31R]
      ring
    · change decodeM b = _
      rw [hdb, hdb2]
      simp [QuadraticAlgebra.im_mul, decodeCM, qm31R]
      ring

#print axioms m31_add_decode
#print axioms m31_sub_decode
#print axioms cm_add_decode
#print axioms cm_sub_decode
#print axioms mul_by_r_decode
end AspisR1.PoseidonPreparedFieldArithmetic
