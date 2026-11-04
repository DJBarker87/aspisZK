import NFG_Primitive64
set_option autoImplicit false
namespace AspisR1.NFG_ProductOk
open Aeneas Aeneas.Std Result
/-- Named emitted checked primitive result law for every raw-product cut. -/
theorem result (a b : U64) (ha : a.val<NEG_DotDomain.P) (hb : b.val<NEG_DotDomain.P) :
 (a*b : Result U64)=ok (NFG_Primitive64.reply a b) :=
 JFr_TX2_DotBounds.mul a b ha hb
/-- The same returned word has exactly the native natural-number product spec. -/
theorem value (a b : U64) (ha : a.val<NEG_DotDomain.P) (hb : b.val<NEG_DotDomain.P) :
 NEG_ProductAbstraction.Product 64 a.val b.val (NFG_Primitive64.reply a b).val :=
 NFG_Primitive64.law a b ha hb
#print axioms result
#print axioms value
end AspisR1.NFG_ProductOk
