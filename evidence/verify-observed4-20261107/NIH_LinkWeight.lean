import NHU_COMBINED_IMPORT
import RPv_JGa_LinkWeight
import RPv_FJk_CopyWeightValue
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.NIH_LinkWeight
open FIq_Native.pool_v1.pair_forest_copy_terminal
/-- Complete original Result and descriptor value, including both variants and every index. -/
theorem result (l : CompiledPoolV1PairForestLink) (index : U64)
 (variant : PoolV1PairForestCompiledVariantV1) (good : JGa_LinkBounds.Good l) :
 ∃ out, link_weight l index variant=ok out ∧ out.val≤1 ∧
 (out.val : FIv_NativeValue.K)=R0P.copyLinkWeight (FJk_CopyDescriptor.link l)
 index.val (FJk_CopyDescriptor.variant variant) := by
 obtain ⟨out,run⟩:=JGa_LinkWeight.source l index variant good
 have exactValue:=FJk_CopyWeightValue.value (K:=FIv_NativeValue.K) l index variant out good run
 exact ⟨out,run,exactValue.2,exactValue.1⟩
/-- Native branch/shift domain follows from the SAME actual compiled link. -/
theorem caller (l : CompiledPoolV1PairForestLink) (member : l∈constants.COPY_LINKS.val) :
 l.weight_kind.val≤4 ∧ l.weight_level.val<64 := by
 have good:=JGa_LinkBounds.all l member
 exact ⟨good.2.2.2.1,good.2.2.2.2⟩
#print axioms result
#print axioms caller
end AspisR1.NIH_LinkWeight
end
