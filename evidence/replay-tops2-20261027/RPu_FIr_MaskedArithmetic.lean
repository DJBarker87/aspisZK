import RPt_FIp_SemanticValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIr_MaskedArithmetic
open Aeneas Aeneas.Std Result
open FIp_SemanticArithmetic (MQ)
open FIp_SemanticValues (Canon decode)

theorem value (eta terminal extra mask etaTerminal masked running : MQ)
    (he : Canon eta) (ht : Canon terminal) (hx : Canon extra) (hm : Canon mask)
    (mul : FIp_SemanticArithmetic.mul eta terminal=ok etaTerminal)
    (add : FIp_SemanticArithmetic.add mask etaTerminal=ok masked)
    (final : FIp_SemanticArithmetic.add masked extra=ok running) :
    Canon running ∧ decode running=decode mask+decode eta*decode terminal+decode extra := by
  have product := FIp_SemanticValues.mul eta terminal etaTerminal he ht mul
  have sum := FIp_SemanticValues.add mask etaTerminal masked hm product.1 add
  have result := FIp_SemanticValues.add masked extra running sum.1 hx final
  exact ⟨result.1,by rw [result.2,sum.2,product.2]⟩

#print axioms value
end AspisR1.FIr_MaskedArithmetic
end
