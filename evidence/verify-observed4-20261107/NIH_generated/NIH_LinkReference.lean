import NIH_LinkWeight
import NDE_LinkBridge
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.NIH_LinkReference
open FIq_Native.pool_v1.pair_forest_copy_terminal
/-- The pinned safe-reference extraction agrees on the COMPLETE original carrier. -/
theorem source (link : CompiledPoolV1PairForestLink) (index : U64)
 (variant : PoolV1PairForestCompiledVariantV1) :
 NDE_Reference5.link_weight_ref link.weight_kind link.weight_level index
 (NDE_LinkBridge.isWithdrawal variant)=link_weight link index variant :=
 NDE_LinkBridge.link_weight link index variant
/-- No success restriction is used to install the descriptor value. -/
theorem result (link : CompiledPoolV1PairForestLink) (index : U64)
 (variant : PoolV1PairForestCompiledVariantV1) (good : JGa_LinkBounds.Good link) :
 ∃ out,NDE_Reference5.link_weight_ref link.weight_kind link.weight_level index
 (NDE_LinkBridge.isWithdrawal variant)=ok out ∧ out.val≤1 ∧
 (out.val : FIv_NativeValue.K)=R0P.copyLinkWeight (FJk_CopyDescriptor.link link)
 index.val (FJk_CopyDescriptor.variant variant) := by
 rw [source]
 exact NIH_LinkWeight.result link index variant good
#print axioms source
#print axioms result
end AspisR1.NIH_LinkReference
end
