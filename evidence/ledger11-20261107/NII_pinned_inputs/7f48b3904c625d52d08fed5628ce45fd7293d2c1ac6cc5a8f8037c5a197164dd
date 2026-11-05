import NGT_BlockAssociation
import NGN_ScalarDomains
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGT_CallerInterface
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

/-- The scalar does not inspect unrelated boundary fields. This is the exact
withCandidateSamplers interface of NGN S1–S4, for every base dictionary. -/
theorem scalar_dictionary (sampling : PreparedModel.Boundaries) {H : Type}
 (D : aspis_core.Digest32 H) (before : transcript.Transcript H)
 (row : U8) (payload : Slice U8) (mode : Bool) :
 PreparedModel.scalar (AspisR1ClaimPreparedBridge.withCandidateSamplers sampling)
   D before row payload mode=
 PreparedModel.scalar NGT_NBA_Installed.actual.sampling D before row payload mode := rfl

/-- NGN S6 uses the actual frozen from-QM constructor, not an arbitrary B field. -/
theorem rho_dictionary (sampling : PreparedModel.Boundaries) {H : Type}
 (D : aspis_core.Digest32 H) (before : transcript.Transcript H)
 (row : U8) (payload : Slice U8) :
 PreparedModel.scalar_k (PreparedFromQmSourceBridge.withSourceFromQm sampling)
   D before row payload=
 PreparedModel.scalar_k NGT_NBA_Installed.actual.sampling D before row payload := rfl

theorem scalar (sampling : PreparedModel.Boundaries) {H : Type}
 (D : aspis_core.Digest32 H) (before : transcript.Transcript H)
 (row : U8) (payload : Slice U8) (mode : Bool)
 (b : NGT_NBL_BlockTrace.Block D before row payload) (out : aspis_core.field.WideExact)
 (reduction : NGT_Reduction.Scalar b.value mode out) :
 PreparedModel.scalar (AspisR1ClaimPreparedBridge.withCandidateSamplers sampling)
   D before row payload mode=ok (out,{before with state:=b.final}) := by
 rw [scalar_dictionary]
 exact NGT_SamplerLaw.scalar D before row payload mode b out reduction

theorem scalar_k (sampling : PreparedModel.Boundaries) {H : Type}
 (D : aspis_core.Digest32 H) (before : transcript.Transcript H)
 (row : U8) (payload : Slice U8)
 (b : NGT_NBL_BlockTrace.Block D before row payload) (out : aspis_core.field.QM31)
 (reduction : NGT_Reduction.K b.value out) :
 PreparedModel.scalar_k (PreparedFromQmSourceBridge.withSourceFromQm sampling)
   D before row payload=ok (out,{before with state:=b.final}) := by
 rw [rho_dictionary]
 exact NGT_SamplerLaw.scalar_k D before row payload b out reduction

/-- Direct consumer at NGN S1: SAME returned gamma and next transcript state;
the already CLOSED powers29 domain is derived at this cut, not assumed. -/
theorem gamma_powers (sampling : PreparedModel.Boundaries) {H : Type}
 (D : aspis_core.Digest32 H) (before : transcript.Transcript H) (payload : Slice U8)
 (b : NGT_NBL_BlockTrace.Block D before 27#u8 payload) (out : aspis_core.field.WideExact)
 (reduction : NGT_Reduction.Scalar b.value true out) :
 ∃ g, FIo_Native.weights.powers 29#usize (NFW_SampledDomains.toNative out)=ok g ∧
 AspisR1ClaimPreparedBridge.powersPublic 29#usize out=
   ok (NFW_PowersCohort.mapArray NFW_PowersCohort.toPublic g) ∧
 (∀ x∈g.val,NFN_LPi_FieldValues.canonE x) :=
 NGN_ScalarDomains.gamma_powers sampling D before _ payload out
   (scalar sampling D before 27#u8 payload true b out reduction)
#print axioms scalar_dictionary
#print axioms rho_dictionary
#print axioms scalar
#print axioms scalar_k
#print axioms gamma_powers
end AspisR1.NGT_CallerInterface
