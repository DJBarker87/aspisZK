import NFF_RawTypedLog
set_option autoImplicit false
namespace AspisR1.NFG_RawDomains
open Aeneas Aeneas.Std
/-- Derives the native opaque-product bound from the root's canonical words. -/
theorem replies (x y : NFF_RawTypedLog.Q)
 (hx : NFE_NFC_RawValues.Canon x) (hy : NFE_NFC_RawValues.Canon y)
 (p : NFF_RawLog.Log)
 (law : ∀ i,NEG_ProductAbstraction.Product 64
  (NFF_RawLog.operands (NFF_RawTypedLog.words x) (NFF_RawTypedLog.words y) i).1
  (NFF_RawLog.operands (NFF_RawTypedLog.words x) (NFF_RawTypedLog.words y) i).2 (p i)) :
 ∀ i,p i≤4611686009837453316 := by
 have domain:=NFF_RawTypedLog.operands x y hx hy
 rw [NFF_RawLog.same_log _ _ p domain law]
 intro i
 have bound:=NEG_DotDomain.instantiate _ _ (domain i).1 (domain i).2
 simpa [NFF_RawLog.exactProducts,NEG_DotDomain.B,NEG_DotDomain.P] using bound
#print axioms replies
end AspisR1.NFG_RawDomains
