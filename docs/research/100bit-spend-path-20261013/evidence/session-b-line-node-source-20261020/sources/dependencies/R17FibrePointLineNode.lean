import R17FibrePointActualSuccess
import R1ZQueryGeometryValuesV6

set_option autoImplicit false

namespace R17FibrePointLineNode
open AspisR1QueryGeometryActual AspisCircleGroupOrder

/-- The actual successful extracted fibre-point output supplies the x-value
used by the maintained query line-node geometry. -/
theorem successful_call_line_node
    (ops : CM31Ops) (hspec : R17FibrePointDecodedProduct.CM31OpsSemantics ops)
    (u : domain.FibreIndex) (hu : u.val < 262144)
    (point : domain.Point field.M31)
    (hcall : fast_domain.fibre_point ops u = .ok point) :
    2 * (R17FibrePointDecodedProduct.decodePoint point).1 ^ 2 - 1 =
      R1ZQueryGeometryValuesV1.sourceLineNode (⟨u.val, hu⟩ : Fin 262144) := by
  have hstored := R17FibrePointActualSuccess.successful_call_eq_stored
    ops hspec u hu point hcall
  have hX : (R17FibrePointDecodedProduct.decodePoint point).1 =
      X (AspisV7ExactOneFoldDomains.storedInitialFibrePoint20
        (⟨u.val, hu⟩ : Fin 262144)) := by
    have hx := congrArg R17TableBasePowerBridge.ZC.re hstored
    change (point.x.val : ZMod 2147483647) =
      (AspisV7ExactOneFoldDomains.storedInitialFibrePoint20
        (⟨u.val, hu⟩ : Fin 262144)).1.1 at hx
    change (point.x.val : ZMod 2147483647) =
      (AspisV7ExactOneFoldDomains.storedInitialFibrePoint20
        (⟨u.val, hu⟩ : Fin 262144)).1.1
    exact hx
  calc
    2 * (R17FibrePointDecodedProduct.decodePoint point).1 ^ 2 - 1 =
        2 * X (AspisV7ExactOneFoldDomains.storedInitialFibrePoint20
          (⟨u.val, hu⟩ : Fin 262144)) ^ 2 - 1 := by rw [hX]
    _ = R1ZQueryGeometryValuesV1.sourceLineNode
          (⟨u.val, hu⟩ : Fin 262144) := rfl

/-- Rephrases the same actual output in the retained stored FirstLineX18
carrier used by the query geometry model. -/
theorem successful_call_stored_line_x
    (ops : CM31Ops) (hspec : R17FibrePointDecodedProduct.CM31OpsSemantics ops)
    (u : domain.FibreIndex) (hu : u.val < 262144)
    (point : domain.Point field.M31)
    (hcall : fast_domain.fibre_point ops u = .ok point) :
    2 * (R17FibrePointDecodedProduct.decodePoint point).1 ^ 2 - 1 =
      AspisV7ExactOneFoldDomains.storedFirstLineX18
        (⟨u.val, hu⟩ : Fin 262144) := by
  rw [successful_call_line_node ops hspec u hu point hcall]
  exact R1ZQueryGeometryValuesV1.sourceLineNode_eq_stored
    (⟨u.val, hu⟩ : Fin 262144)

#print axioms successful_call_line_node
#print axioms successful_call_stored_line_x
end R17FibrePointLineNode
