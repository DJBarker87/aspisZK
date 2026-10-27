import R1SemanticOpening
import R1SemanticTransport
import R0P.Copy
import R1SelectedCircleWeightModel

/-! A mathematical selected-row construction for the seven opening
functionals. The circle rows use the existing natural-line `circleWeight`
model. This file does not prove that this model matches the current Rust
`Weights` implementation. -/

set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section

namespace AspisR1.SelectedOpeningFunctionals

open AspisCircleGroupOrder

variable {E : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod P) E]

def alpha (cs : List E) : Fin 10 → E := fun j => cs.getD (15 + j.val) 0

def circle (z : Fin 2 → AspisR0.ChordGeometry.Point E) :
    Fin 2 → Fin 1024 → E := fun k j =>
      AspisR1.SelectedCircleWeightModel.circleWeight (z k).val.1 (z k).val.2 j.val

def rows (cs : List E) (z : Fin 2 → AspisR0.ChordGeometry.Point E) :
    Fin 7 → Fin 1024 → E :=
  AspisR1.SemanticOpening.rows R0P.copyInactiveRows
    (AspisR1.SemanticTransport.points (alpha cs))
    (R0P.SemSource.libraWeight (alpha cs)) (circle z)

def functionals (cs : List E) (z : Fin 2 → AspisR0.ChordGeometry.Point E) :=
  AspisR1.RawFunctionalWeights.rawFunctionals (RingHom.id E) (rows cs z)

def rawBase (cs : List E) (z : Fin 2 → AspisR0.ChordGeometry.Point E) :=
  AspisR1.RawFunctionalWeights.rawBaseFunctional (RingHom.id E) (rows cs z)

theorem rows_point (cs : List E) (z : Fin 2 → AspisR0.ChordGeometry.Point E)
    (j : Fin 3) :
    rows cs z ⟨j.val + 1, by omega⟩ =
      AspisR1.tensorPoint (AspisR1.SemanticTransport.points (alpha cs) j) :=
  AspisR1.SemanticOpening.rows_point R0P.copyInactiveRows
    (AspisR1.SemanticTransport.points (alpha cs))
    (R0P.SemSource.libraWeight (alpha cs)) (circle z) j

theorem functionals_eq_rows (cs : List E)
    (z : Fin 2 → AspisR0.ChordGeometry.Point E) :
    functionals cs z =
      AspisR1.RawFunctionalWeights.rawFunctionals (RingHom.id E) (rows cs z) := rfl

theorem rawBase_eq_rows (cs : List E)
    (z : Fin 2 → AspisR0.ChordGeometry.Point E) :
    rawBase cs z =
      AspisR1.RawFunctionalWeights.rawBaseFunctional (RingHom.id E) (rows cs z) := rfl

#print axioms rows_point
#print axioms functionals_eq_rows
#print axioms rawBase_eq_rows

end AspisR1.SelectedOpeningFunctionals
end
