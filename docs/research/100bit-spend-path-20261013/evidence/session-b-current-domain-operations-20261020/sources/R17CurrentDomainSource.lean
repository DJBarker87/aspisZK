import R17CurrentCM31Semantics

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace R17CurrentDomainSource
open AspisR1QueryGeometryActual

/-- Concrete retained checked CM31 operations discharge the arithmetic
premise of the successful extracted fibre-point caller. -/
theorem successful_fibre_point_stored
    (u : domain.FibreIndex) (hu : u.val < 262144)
    (point : domain.Point field.M31)
    (h : fast_domain.fibre_point R17CurrentCM31Semantics.operations u = .ok point) :
    (⟨(R17FibrePointDecodedProduct.decodePoint point).1,
       (R17FibrePointDecodedProduct.decodePoint point).2⟩ :
       R17TableBasePowerBridge.ZC) =
      R17TableCirclePowerBridge.circleCoords
        (AspisV7ExactOneFoldDomains.storedInitialFibrePoint20
          (⟨u.val,hu⟩ : Fin 262144)) := by
  exact R17FibrePointActualSuccess.successful_call_eq_stored
    R17CurrentCM31Semantics.operations R17CurrentCM31Semantics.operations_semantics
    u hu point h

/-- Concrete retained checked M31 and CM31 operations discharge both
arithmetic premises of the exact source-parameterized line-node body. -/
theorem successful_line_node_stored
    (u : domain.FibreIndex) (hu : u.val < 262144) (out : field.M31)
    (h : R17FibrePointLineNodeActual.line_node
      R17CurrentCM31Semantics.operations R17CurrentM31Semantics.operations u = .ok out) :
    R17FibrePointLineNodeActual.decoded out =
      AspisV7ExactOneFoldDomains.storedFirstLineX18 (⟨u.val,hu⟩ : Fin 262144) := by
  exact R17FibrePointLineNodeActual.successful_line_node_stored
    R17CurrentCM31Semantics.operations R17CurrentCM31Semantics.operations_semantics
    R17CurrentM31Semantics.operations R17CurrentM31Semantics.operations_semantics
    u hu out h

#print axioms successful_fibre_point_stored
#print axioms successful_line_node_stored
end R17CurrentDomainSource
