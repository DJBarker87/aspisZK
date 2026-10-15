import R1RawOpening
import R1SelectedOpeningFunctionals

/-! If matching data already stores the selected literal functionals and
base functional, the corresponding raw-row update is the identity. This is
deterministic record plumbing only. -/
set_option autoImplicit false
noncomputable section

namespace AspisR1.LiteralOpeningDataRows

open AspisCircleGroupOrder
open AspisR1.MatchingSupport

variable {E : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod P) E]

theorem withRows_eq_self
    (d : MatchingSupport.Data E)
    (cs : List E)
    (z : Fin 2 → AspisR0.ChordGeometry.Point E)
    (hF : d.F = SelectedOpeningFunctionals.functionals cs z)
    (hF0 : d.F0 = SelectedOpeningFunctionals.rawBase cs z) :
    RawOpening.withRows (RingHom.id E)
      (SelectedOpeningFunctionals.rows cs z) d = d := by
  have hF' : d.F =
      RawFunctionalWeights.rawFunctionals (RingHom.id E)
        (SelectedOpeningFunctionals.rows cs z) :=
    hF.trans (SelectedOpeningFunctionals.functionals_eq_rows cs z)
  have hF0' : d.F0 =
      RawFunctionalWeights.rawBaseFunctional (RingHom.id E)
        (SelectedOpeningFunctionals.rows cs z) :=
    hF0.trans (SelectedOpeningFunctionals.rawBase_eq_rows cs z)
  unfold RawOpening.withRows
  rw [← hF', ← hF0']

#print axioms withRows_eq_self

end AspisR1.LiteralOpeningDataRows
end
