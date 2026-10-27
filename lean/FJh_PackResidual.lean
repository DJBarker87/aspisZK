import FJe_PackingLinear
set_option autoImplicit false
namespace AspisR1.FJh_PackResidual
variable {K : Type} [Field K]
/-- Pack the exact three-branch residual without expanding any round body. -/
theorem value (i u block a b c : K) (t l f n : Fin 4 → K) :
    block*(a*(R0P.poseidonPackingFormula i u t-R0P.poseidonPackingFormula i u l)+
      b*(R0P.poseidonPackingFormula i u t-R0P.poseidonPackingFormula i u f)+
      c*(R0P.poseidonPackingFormula i u t-R0P.poseidonPackingFormula i u n))=
    R0P.poseidonPackingFormula i u
      (fun j=>block*(a*(t j-l j)+b*(t j-f j)+c*(t j-n j))) := by
  unfold R0P.poseidonPackingFormula
  ring
#print axioms value
end AspisR1.FJh_PackResidual
