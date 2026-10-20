import AspisFormal.V5FriConcreteEncoderCommutation
import LineFold
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Field interpretation of verifier.rs:105–126,169–186. These definitions
are specifications of the source expressions, not extracted executions. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.FoldRuntimeAlgebra
open AspisV5ComponentCConcreteFoldLinearity
variable {K : Type*} [Field K]

def line (alpha x y z : K) (v : Fin 4 → K) : K :=
  let h0 := (v 0 + v 1 + v 2 + v 3) / 4
  let h2 := (v 0 + v 1 - v 2 - v 3) / (4 * z)
  let c0 := (v 0 - v 1) / (2 * x)
  let c1 := (v 3 - v 2) / (2 * y)
  let h1 := (c0 + c1) / 2
  let h3 := (c0 - c1) / (2 * z)
  h0 + alpha * (h1 + alpha * (h2 + alpha * h3))

def circle (alpha x y : K) (v : Fin 4 → K) : K :=
  (v 0 + v 1 + v 2 + v 3) / 4 + alpha *
    ((v 0 - v 1 - v 2 + v 3) / (4 * y) + alpha *
      ((v 0 + v 1 - v 2 - v 3) / (4 * x) + alpha *
        ((v 0 - v 1 + v 2 - v 3) / (4 * x * y))))

/-- Field expression of verifier.rs:178–186 after the five-slot read. -/
def lineWithInverses (alpha ix iy iz : K) (v : Fin 4 → K) : K :=
  let h0 := (v 0 + v 1 + v 2 + v 3) * (4 : K)⁻¹
  let h2 := (v 0 + v 1 - v 2 - v 3) * ((4 : K)⁻¹ * iz)
  let c0 := (v 0 - v 1) * ((2 : K)⁻¹ * ix)
  let c1 := (v 3 - v 2) * ((2 : K)⁻¹ * iy)
  let h1 := (c0 + c1) * (2 : K)⁻¹
  let h3 := (c0 - c1) * ((2 : K)⁻¹ * iz)
  h0 + alpha * (h1 + alpha * (h2 + alpha * h3))

def circleWithInverses (alpha ix iy : K) (v : Fin 4 → K) : K :=
  (v 0 + v 1 + v 2 + v 3) * (4 : K)⁻¹ + alpha *
    ((v 0 - v 1 - v 2 + v 3) * ((4 : K)⁻¹ * iy) + alpha *
      ((v 0 + v 1 - v 2 - v 3) * ((4 : K)⁻¹ * ix) + alpha *
        ((v 0 - v 1 + v 2 - v 3) * ((4 : K)⁻¹ * ix * iy))))

theorem line_with_inverses_eq (alpha x y z : K) (v : Fin 4 → K) :
    lineWithInverses alpha x⁻¹ y⁻¹ z⁻¹ v = line alpha x y z v := by
  simp only [lineWithInverses, line, div_eq_mul_inv, mul_inv_rev]
  ring

theorem circle_with_inverses_eq (alpha x y : K) (v : Fin 4 → K) :
    circleWithInverses alpha x⁻¹ y⁻¹ v = circle alpha x y v := by
  simp only [circleWithInverses, circle, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Source slot 3 has coordinate y; the model's second pair starts at -y. -/
theorem line_eq_model (alpha x y z : K) (v : Fin 4 → K)
    (h2 : (2 : K) ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    line alpha x y z v =
      lineFoldValue alpha (2 * x)⁻¹ (2 * -y)⁻¹ (2 * z)⁻¹ v := by
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by ring
    rw [this]; exact mul_ne_zero h2 h2
  unfold line lineFoldValue pairFoldValue
  field_simp [h2, h4, hx, hy, hz]
  ring

/-- The circle quartet is (x,y),(x,-y),(-x,-y),(-x,y). -/
theorem circle_eq_model (alpha x y : K) (v : Fin 4 → K)
    (h2 : (2 : K) ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) :
    circle alpha x y v =
      lineFoldValue alpha (2 * y)⁻¹ (2 * -y)⁻¹ (2 * x)⁻¹ v := by
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by ring
    rw [this]; exact mul_ne_zero h2 h2
  unfold circle lineFoldValue pairFoldValue
  field_simp [h2, h4, hx, hy]
  ring

/-- Direct bridge to the recovery theorem in the requested LineFold model. -/
theorem line_recovers_channels (h0 h1 h2 h3 x y z alpha : K)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hchar : (2 : K) ≠ 0) :
    line alpha x y z
      ![AspisR1.a h0 h1 h2 h3 x y z, AspisR1.b h0 h1 h2 h3 x y z,
        AspisR1.c h0 h1 h2 h3 x y z, AspisR1.d h0 h1 h2 h3 x y z] =
      h0 + alpha * (h1 + alpha * (h2 + alpha * h3)) := by
  simpa [line, AspisR1.C0, AspisR1.C1] using
    AspisR1.recovered_horner h0 h1 h2 h3 x y z hx hy hz hchar alpha

/-- One backward batch-inversion step; no vector length is evaluated. -/
theorem batch_inverse_entry (pre value post : K)
    (hp : pre ≠ 0) (hv : value ≠ 0) (hs : post ≠ 0) :
    (pre * value * post)⁻¹ * post * pre = value⁻¹ := by
  field_simp [hp, hv, hs]

/-- The backward invariant advances from an entry to its pre. -/
theorem batch_inverse_step (pre value : K) (hp : pre ≠ 0)
    (hv : value ≠ 0) : (pre * value)⁻¹ * value = pre⁻¹ := by
  field_simp [hp, hv]

#print axioms line_with_inverses_eq
#print axioms circle_with_inverses_eq
#print axioms line_recovers_channels
#print axioms line_eq_model
#print axioms circle_eq_model
#print axioms batch_inverse_entry
#print axioms batch_inverse_step
end AspisR1.FoldRuntimeAlgebra
