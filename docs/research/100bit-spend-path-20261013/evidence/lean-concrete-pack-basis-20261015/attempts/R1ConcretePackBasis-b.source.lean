import R1ExactBaseProjection
import R0P.CoreExt

/-! A concrete mathematical basis for the four-coordinate packing map in the
exact retained tower. This is algebraic basis plumbing only; it does not
refine the optimized Rust limb implementation. -/

set_option autoImplicit false

namespace AspisR1.ConcretePackBasis

open AspisV8R15.ExactTowerBase
open AspisWideTower

abbrev E := WideExact
abbrev F := AspisR1.ExactBaseProjection.embed.fieldRange

/-- The image of the CM31 generator in the exact wide tower. -/
def iE : E :=
  (algebraMap QM31Exact WideExact)
    ((algebraMap CM31Exact QM31Exact) AspisWideTower.cm31I)

/-- The image of the QM31 generator in the exact wide tower. -/
def uE : E :=
  (algebraMap QM31Exact WideExact) AspisWideTower.wideU

/-- In these nested quadratic coordinates, the four packed coefficients are
exactly the first four coordinates of WideExact. -/
theorem packing_coordinates (a b c d : M31Exact) :
    AspisR1.ExactBaseProjection.embed a +
        iE * AspisR1.ExactBaseProjection.embed b +
        uE * AspisR1.ExactBaseProjection.embed c +
        iE * uE * AspisR1.ExactBaseProjection.embed d =
      (⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, 0⟩ : WideExact) := by
  ext <;> simp [iE, uE, AspisR1.ExactBaseProjection.embed,
    AspisWideTower.cm31I, AspisWideTower.wideU, mul_add, add_mul,
    mul_assoc, add_assoc]

/-- `{1, i, u, i*u}` is linearly independent over the embedded M31 base. -/
def basis : R0P.PackBasis F where
  i := iE
  u := uE
  indep := by
    intro a b c d ha hb hc hd hsum
    obtain ⟨a₀, ha₀⟩ := RingHom.mem_fieldRange.mp ha
    obtain ⟨b₀, hb₀⟩ := RingHom.mem_fieldRange.mp hb
    obtain ⟨c₀, hc₀⟩ := RingHom.mem_fieldRange.mp hc
    obtain ⟨d₀, hd₀⟩ := RingHom.mem_fieldRange.mp hd
    have hz :
        (⟨⟨⟨a₀, b₀⟩, ⟨c₀, d₀⟩⟩, 0⟩ : WideExact) = 0 := by
      rw [← ha₀, ← hb₀, ← hc₀, ← hd₀, packing_coordinates] at hsum
      exact hsum
    have h₀ : a₀ = 0 := by
      have h := congrArg (fun z : WideExact => z.re.re.re) hz
      simpa using h
    have h₁ : b₀ = 0 := by
      have h := congrArg (fun z : WideExact => z.re.re.im) hz
      simpa using h
    have h₂ : c₀ = 0 := by
      have h := congrArg (fun z : WideExact => z.re.im.re) hz
      simpa using h
    have h₃ : d₀ = 0 := by
      have h := congrArg (fun z : WideExact => z.re.im.im) hz
      simpa using h
    constructor
    · calc
        a = AspisR1.ExactBaseProjection.embed a₀ := ha₀.symm
        _ = AspisR1.ExactBaseProjection.embed 0 := by rw [h₀]
        _ = 0 := map_zero _
    constructor
    · calc
        b = AspisR1.ExactBaseProjection.embed b₀ := hb₀.symm
        _ = AspisR1.ExactBaseProjection.embed 0 := by rw [h₁]
        _ = 0 := map_zero _
    constructor
    · calc
        c = AspisR1.ExactBaseProjection.embed c₀ := hc₀.symm
        _ = AspisR1.ExactBaseProjection.embed 0 := by rw [h₂]
        _ = 0 := map_zero _
    · calc
        d = AspisR1.ExactBaseProjection.embed d₀ := hd₀.symm
        _ = AspisR1.ExactBaseProjection.embed 0 := by rw [h₃]
        _ = 0 := map_zero _

#print axioms packing_coordinates
#print axioms basis

end AspisR1.ConcretePackBasis
