import FJn_MaskValue
import FIr_MaskedArithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_MaskedSourceValue
open Aeneas Aeneas.Std Result
open FIp_SemanticArithmetic (MQ)
open FIp_SemanticValues (Canon decode)
/-- Combine the actual installed mask call and exact source arithmetic tail.
All outputs are retained from that tail; mask canonicality is derived. -/
theorem value (c1 : Array MQ 16#usize) (m : Array MQ 10#usize) (g : MQ)
    (point : Array MQ 10#usize) (eta terminal extra mask product sum running : MQ)
    (hc : ∀ x∈c1.val,Canon x) (hm : ∀ x∈m.val,Canon x) (hp : ∀ x∈point.val,Canon x)
    (hg : Canon g) (he : Canon eta) (ht : Canon terminal) (hx : Canon extra)
    (maskCall : FIp_SemanticArithmetic.mask c1 m g point=ok mask)
    (multiply : FIp_SemanticArithmetic.mul eta terminal=ok product)
    (add : FIp_SemanticArithmetic.add mask product=ok sum)
    (finish : FIp_SemanticArithmetic.add sum extra=ok running) :
    Canon running ∧ decode running=FIp_MaskValue.value c1 m g point+decode eta*decode terminal+decode extra := by
  have maskV:=FJn_MaskValue.value c1 m g point mask hc hm hp hg maskCall
  have result:=FIr_MaskedArithmetic.value eta terminal extra mask product sum running he ht hx maskV.1 multiply add finish
  exact ⟨result.1,result.2.trans (congrArg (fun v=>v+decode eta*decode terminal+decode extra) maskV.2)⟩
#print axioms value
end AspisR1.FJn_MaskedSourceValue
end
