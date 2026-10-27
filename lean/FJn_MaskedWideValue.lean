import FJn_MaskWide
import FIr_MaskedArithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_MaskedWideValue
open Aeneas Aeneas.Std Result
open FIp_SemanticArithmetic (MQ)
open FIp_SemanticValues (Canon decode)
open FIz_ConcretePack (embed)
/-- Complete source masking arithmetic in Wide, retaining exact native calls
and all actual returned operands. Literal-frame identification is downstream. -/
theorem value (c1 : Array MQ 16#usize) (m : Array MQ 10#usize) (g : MQ)
    (point : Array MQ 10#usize) (eta terminal extra mask product sum running : MQ)
    (hc : ∀ x∈c1.val,Canon x) (hm : ∀ x∈m.val,Canon x) (hp : ∀ x∈point.val,Canon x)
    (hg : Canon g) (he : Canon eta) (ht : Canon terminal) (hx : Canon extra)
    (maskCall : FIp_SemanticArithmetic.mask c1 m g point=ok mask)
    (multiply : FIp_SemanticArithmetic.mul eta terminal=ok product)
    (add : FIp_SemanticArithmetic.add mask product=ok sum)
    (finish : FIp_SemanticArithmetic.add sum extra=ok running) :
    Canon running ∧ embed (decode running)=
      R0P.Mask.maskValue ConcretePackBasis.basis (FJn_MaskWide.cell c1) (FJn_MaskWide.cell m)
        (embed (decode g)) (FJn_MaskWide.cell point)+embed (decode eta)*embed (decode terminal)+embed (decode extra) := by
  have maskV:=FJn_MaskWide.value c1 m g point mask hc hm hp hg maskCall
  have result:=FIr_MaskedArithmetic.value eta terminal extra mask product sum running he ht hx maskV.1 multiply add finish
  refine ⟨result.1,?_⟩
  rw [result.2,map_add,map_add,map_mul]
  exact congrArg (fun v=>v+embed (decode eta)*embed (decode terminal)+embed (decode extra)) maskV.2
#print axioms value
end AspisR1.FJn_MaskedWideValue
end
