import FJb_ExternalExact
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_PackingLinear
variable {K : Type} [CommRing K]
/-- The four tower functionals are linear on the same four operands. -/
theorem add (i u : K) (a b : Fin 4 → K) :
    R0P.poseidonPackingFormula i u (fun j => a j + b j) =
      R0P.poseidonPackingFormula i u a + R0P.poseidonPackingFormula i u b := by
  unfold R0P.poseidonPackingFormula
  ring
/-- The source's ordered four-way sum, with its initial zero preserved. -/
theorem ordered_sum (i u : K) (a b c d : Fin 4 → K) :
    R0P.poseidonPackingFormula i u (fun j => (((0+a j)+b j)+c j)+d j) =
      (((0+R0P.poseidonPackingFormula i u a)+
        R0P.poseidonPackingFormula i u b)+R0P.poseidonPackingFormula i u c)+
        R0P.poseidonPackingFormula i u d := by
  unfold R0P.poseidonPackingFormula
  ring
#print axioms add
#print axioms ordered_sum
end AspisR1.FJe_PackingLinear
end
