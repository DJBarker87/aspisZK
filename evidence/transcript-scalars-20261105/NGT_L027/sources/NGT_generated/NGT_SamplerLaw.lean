import NGT_EmittedEq
import NGT_Reduction
import NGT_NBL_BlockTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGT_SamplerLaw
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

/-- Native reduction trace at the block from THIS three-digest execution.
Input state, payload and final state are not independently selected. -/
theorem scalar {H : Type} (D : aspis_core.Digest32 H)
 (before : transcript.Transcript H) (row : U8) (payload : Slice U8) (mode : Bool)
 (b : NGT_NBL_BlockTrace.Block D before row payload) (out : aspis_core.field.WideExact)
 (reduction : NGT_Reduction.Scalar b.value mode out) :
 PreparedModel.scalar NGT_NBA_Installed.actual.sampling D before row payload mode=
   ok (out,{before with state:=b.final}) := by
 unfold PreparedModel.scalar
 rw [NGT_NBL_BlockTrace.block_result D before row payload b,bind_tc_ok]
 simp only [Aeneas.Std.uncurry]
 rw [NGT_Reduction.scalar reduction,bind_tc_ok]
 rfl

theorem scalar_k {H : Type} (D : aspis_core.Digest32 H)
 (before : transcript.Transcript H) (row : U8) (payload : Slice U8)
 (b : NGT_NBL_BlockTrace.Block D before row payload) (out : aspis_core.field.QM31)
 (reduction : NGT_Reduction.K b.value out) :
 PreparedModel.scalar_k NGT_NBA_Installed.actual.sampling D before row payload=
   ok (out,{before with state:=b.final}) := by
 have embed : NGT_NBA_Installed.actual.sampling.fromQm out=
   ok (PreparedFromQmSourceBridge.fromQmEmbedding out) :=
   PreparedFromQmSourceBridge.fromQmSource_success out
 unfold PreparedModel.scalar_k
 rw [NGT_NBL_BlockTrace.block_result D before row payload b,bind_tc_ok]
 simp only [Aeneas.Std.uncurry]
 rw [NGT_Reduction.scalar_k reduction,bind_tc_ok]
 simp only [lift,bind_tc_ok,embed]
 rfl

theorem emitted_scalar {H : Type} (D : aspis_core.Digest32 H)
 (before : transcript.Transcript H) (row : U8) (payload : Slice U8) (mode : Bool)
 (b : NGT_NBL_BlockTrace.Block D before row payload) (out : aspis_core.field.WideExact)
 (reduction : NGT_Reduction.Scalar b.value mode out) :
 NGT_Emitted.scalar NGT_NBA_Installed.actual.sampling D before row payload mode=
   ok (out,{before with state:=b.final}) := by
 rw [NGT_EmittedEq.scalar]
 exact scalar D before row payload mode b out reduction

theorem emitted_scalar_k {H : Type} (D : aspis_core.Digest32 H)
 (before : transcript.Transcript H) (row : U8) (payload : Slice U8)
 (b : NGT_NBL_BlockTrace.Block D before row payload) (out : aspis_core.field.QM31)
 (reduction : NGT_Reduction.K b.value out) :
 NGT_Emitted.scalar_k NGT_NBA_Installed.actual.sampling D before row payload=
   ok (out,{before with state:=b.final}) := by
 rw [NGT_EmittedEq.scalar_k]
 exact scalar_k D before row payload b out reduction
#print axioms scalar
#print axioms scalar_k
#print axioms emitted_scalar
#print axioms emitted_scalar_k
end AspisR1.NGT_SamplerLaw
