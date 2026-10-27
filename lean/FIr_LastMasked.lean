import FIr_LastLiteral
import FIr_MaskedArithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIr_LastMasked
open Aeneas Aeneas.Std Result
open FIp_SemanticArithmetic (MQ)
open FIp_SemanticValues (Canon decode)
abbrev K := ExtractedMaskQM31Exact.QM31Exact
abbrev W := AspisWideTower.WideExact

theorem value (literal : W) (eta terminal extra mask etaTerminal masked running : MQ)
    (last : literal=algebraMap K W (decode running))
    (he : Canon eta) (ht : Canon terminal) (hx : Canon extra) (hm : Canon mask)
    (mul : FIp_SemanticArithmetic.mul eta terminal=ok etaTerminal)
    (add : FIp_SemanticArithmetic.add mask etaTerminal=ok masked)
    (final : FIp_SemanticArithmetic.add masked extra=ok running) :
    literal=algebraMap K W (decode mask)+algebraMap K W (decode eta)*
      algebraMap K W (decode terminal)+algebraMap K W (decode extra) := by
  have arithmetic := (FIr_MaskedArithmetic.value eta terminal extra mask etaTerminal masked running he ht hx hm mul add final).2
  rw [last,arithmetic,map_add,map_add,map_mul]

#print axioms value
end AspisR1.FIr_LastMasked
end
