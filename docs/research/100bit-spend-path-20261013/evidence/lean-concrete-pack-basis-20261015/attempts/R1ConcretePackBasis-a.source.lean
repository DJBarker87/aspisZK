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
    have ha' : a = AspisR1.ExactBaseProjection.embed
        (AspisR1.ExactBaseProjection.project a) :=
      (AspisR1.ExactBaseProjection.mem_fieldRange_iff_project a).mp ha |>.symm
    have hb' : b = AspisR1.ExactBaseProjection.embed
        (AspisR1.ExactBaseProjection.project b) :=
      (AspisR1.ExactBaseProjection.mem_fieldRange_iff_project b).mp hb |>.symm
    have hc' : c = AspisR1.ExactBaseProjection.embed
        (AspisR1.ExactBaseProjection.project c) :=
      (AspisR1.ExactBaseProjection.mem_fieldRange_iff_project c).mp hc |>.symm
    have hd' : d = AspisR1.ExactBaseProjection.embed
        (AspisR1.ExactBaseProjection.project d) :=
      (AspisR1.ExactBaseProjection.mem_fieldRange_iff_project d).mp hd |>.symm
    have hz :
        (⟨⟨⟨AspisR1.ExactBaseProjection.project a,
              AspisR1.ExactBaseProjection.project b⟩,
            ⟨AspisR1.ExactBaseProjection.project c,
              AspisR1.ExactBaseProjection.project d⟩⟩, 0⟩ : WideExact) = 0 := by
      rw [ha', hb', hc', hd', packing_coordinates] at hsum
      exact hsum
    have h₀ : AspisR1.ExactBaseProjection.project a = 0 := by
      have h := congrArg (fun z : WideExact => z.re.re.re) hz
      simpa using h
    have h₁ : AspisR1.ExactBaseProjection.project b = 0 := by
      have h := congrArg (fun z : WideExact => z.re.re.im) hz
      simpa using h
    have h₂ : AspisR1.ExactBaseProjection.project c = 0 := by
      have h := congrArg (fun z : WideExact => z.re.im.re) hz
      simpa using h
    have h₃ : AspisR1.ExactBaseProjection.project d = 0 := by
      have h := congrArg (fun z : WideExact => z.re.im.im) hz
      simpa using h
    constructor
    · simpa only [h₀, map_zero] using ha'
    constructor
    · simpa only [h₁, map_zero] using hb'
    constructor
    · simpa only [h₂, map_zero] using hc'
    · simpa only [h₃, map_zero] using hd'

#print axioms packing_coordinates
#print axioms basis

end AspisR1.ConcretePackBasis
