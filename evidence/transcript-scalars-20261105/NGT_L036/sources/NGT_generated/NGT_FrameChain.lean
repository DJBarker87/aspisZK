import NGT_SamplerLaw
import NGT_RuntimeDomain
import NGT_NBL_InitTrace
import LPk_ReturnChecks
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGT_FrameChain
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

/-- Native byte initialization produces the exact high-to-low word input of
both the four-pass and eight-pass generic division inductions. -/
theorem byte_input {block : Array U8 32#usize}
 {before after : NGT_NBL_InitTrace.Words UInt32}
 (writes : NGT_NBL_InitTrace.Trace (NGT_NBL_InitTrace.byteWord block) 8 before after) :
 after.val.reverse=SamplerBytePass.digits block := NGT_NBL_InitTrace.rho writes

/-- The frozen low-leaf debug assertions follow from the SAME retained trace. -/
theorem low_checks (block : Array U8 32#usize) (digits quotient : Array U32 8#usize)
 (steps : LPk_Induction.Digits 8 (SamplerBytePass.digits block)
   (AspisR1GammaCaller.DigitsModel.values digits)
   (ExtractedQM31SamplerPassLoop.words quotient).reverse) :
 (∀ x∈quotient.val.drop 1,x.val=0) ∧
 (quotient.val[0]'(by rw [quotient.property];decide)).val≤256 :=
 LPk_ReturnChecks.checks block digits quotient steps

theorem scalar {H : Type} (D : aspis_core.Digest32 H)
 (before : transcript.Transcript H) (row : U8) (payload : Slice U8) (mode : Bool)
 (b : NGT_NBL_BlockTrace.Block D before row payload) (out : aspis_core.field.WideExact)
 (reduction : NGT_Reduction.Scalar b.value mode out) :
 PreparedModel.scalar NGT_NBA_Installed.actual.sampling D before row payload mode=
   ok (out,b.after) ∧ b.after.hash=before.hash ∧ b.log.length=3 ∧
 (∀ event∈b.log,D.digest before.hash event.1=ok event.2) := by
 exact ⟨NGT_SamplerLaw.scalar D before row payload mode b out reduction,rfl,
   NGT_NBL_BlockTrace.block_log D before row payload b⟩

theorem scalar_k {H : Type} (D : aspis_core.Digest32 H)
 (before : transcript.Transcript H) (row : U8) (payload : Slice U8)
 (b : NGT_NBL_BlockTrace.Block D before row payload) (out : aspis_core.field.QM31)
 (reduction : NGT_Reduction.K b.value out) :
 PreparedModel.scalar_k NGT_NBA_Installed.actual.sampling D before row payload=
   ok (out,b.after) ∧ b.after.hash=before.hash ∧ b.log.length=3 ∧
 (∀ event∈b.log,D.digest before.hash event.1=ok event.2) := by
 exact ⟨NGT_SamplerLaw.scalar_k D before row payload b out reduction,rfl,
   NGT_NBL_BlockTrace.block_log D before row payload b⟩
#print axioms byte_input
#print axioms low_checks
#print axioms scalar
#print axioms scalar_k
end AspisR1.NGT_FrameChain
