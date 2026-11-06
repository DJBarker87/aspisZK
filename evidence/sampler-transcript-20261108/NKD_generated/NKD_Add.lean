import NBL_AddNative
set_option autoImplicit false
namespace AspisR1.NKD_Add
open Aeneas Aeneas.Std Result ExtractedIndexedAddSmallNatModelV1
/-- Reviewed cut for eight forward native digit/carry steps, including full array writeback. -/
abbrev Cut (digits : Digits) (amount : U32) (out : Digits) (carry : U32) : Prop :=
 NBA_AddCarry.Trace (values digits) amount.val (values out) carry.val
/-- TX1:155: complete return and mutated array; no child endpoint is a hypothesis. -/
theorem root (digits : Digits) (amount : U32) (canonical : Canonical digits)
 (small : amount.val ≤ 257) (out : Digits) (carry : U32) (cut : Cut digits amount out carry) :
 AspisR1Post25SamplerIndexedAddSmallCandidate.sampler.add_small_base_p digits amount =
 ok (carry != 0#u32,out) ∧ Canonical out :=
 ⟨NBL_AddNative.source digits amount canonical small out carry cut,
 NBL_AddNative.canonical digits amount out carry cut⟩
#print root
#print axioms root
end AspisR1.NKD_Add
