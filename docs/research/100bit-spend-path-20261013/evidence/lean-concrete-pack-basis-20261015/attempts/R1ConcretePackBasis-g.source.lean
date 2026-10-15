import R1ExactBaseProjection
import R1GenericPackBasis

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

/-- The concrete coordinate identity implies independence before passing to
coefficients in the embedded field range. -/
theorem independent (a b c d : M31Exact)
    (h : AspisR1.ExactBaseProjection.embed a +
        iE * AspisR1.ExactBaseProjection.embed b +
        uE * AspisR1.ExactBaseProjection.embed c +
        iE * uE * AspisR1.ExactBaseProjection.embed d = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have hz : (⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, 0⟩ : WideExact) = 0 :=
    (packing_coordinates a b c d).symm.trans h
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using congrArg (fun z : WideExact => z.re.re.re) hz
  · simpa using congrArg (fun z : WideExact => z.re.re.im) hz
  · simpa using congrArg (fun z : WideExact => z.re.im.re) hz
  · simpa using congrArg (fun z : WideExact => z.re.im.im) hz

attribute [local irreducible] iE uE AspisR1.ExactBaseProjection.embed

/-- `{1, i, u, i*u}` is independent over the embedded M31 base. -/
noncomputable def basis : R0P.PackBasis F := by
  refine GenericPackBasis.ofEmbedding AspisR1.ExactBaseProjection.embed iE uE ?_
  intro a b c d h
  exact independent a b c d h

#print axioms packing_coordinates
#print axioms independent
#print axioms basis

end AspisR1.ConcretePackBasis
