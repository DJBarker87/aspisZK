import NGN_FrameChain
import NGT_CallerInterface
import NGT_NBA_Installed
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHL_PreparedScalars
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open NFW_PreparedControl NGN_Opening NGN_Cuts
abbrev actual := NGT_NBA_Installed.actual

theorem scalar_dictionary {H : Type} (D : aspis_core.Digest32 H)
 (t : transcript.Transcript H) (row : U8) (payload : Slice U8) (mode : Bool) :
 PreparedModel.scalar actual.sampling D t row payload mode =
 PreparedModel.scalar (AspisR1ClaimPreparedBridge.withCandidateSamplers actual.sampling)
   D t row payload mode := (NGT_CallerInterface.scalar_dictionary _ D t row payload mode).symm

theorem rho_dictionary {H : Type} (D : aspis_core.Digest32 H)
 (t : transcript.Transcript H) (row : U8) (payload : Slice U8) :
 PreparedModel.scalar_k actual.sampling D t row payload =
 PreparedModel.scalar_k (PreparedFromQmSourceBridge.withSourceFromQm actual.sampling)
   D t row payload := (NGT_CallerInterface.rho_dictionary _ D t row payload).symm

/-- S1: the digest trace supplies both the SAME gamma and its next state. -/
theorem gamma {H : Type} (D : aspis_core.Digest32 H) (v : verifier.View)
 (start : transcript.Transcript H) (b : NGT_NBL_BlockTrace.Block D start 27#u8 v.y1)
 (g : aspis_core.field.WideExact) (reduction : NGT_Reduction.Scalar b.value true g) :
 gammaCut actual D v start=kappaCut actual D v g {start with state:=b.final} := by
 apply NGN_FrameChain.gamma_kappa
 rw [scalar_dictionary]
 exact NGT_CallerInterface.scalar _ D start _ _ true b g reduction

/-- S2: serialization remains the actual dictionary's exact byte result. -/
theorem kappa {H : Type} (D : aspis_core.Digest32 H) (v : verifier.View)
 (before : transcript.Transcript H) (g k : aspis_core.field.WideExact)
 (bytes : Array U8 32#usize) (serialize : actual.sampling.toBytes v.inactive=ok bytes)
 (b : NGT_NBL_BlockTrace.Block D before 28#u8 (Array.to_slice bytes))
 (reduction : NGT_Reduction.Scalar b.value false k) :
 kappaCut actual D v g before=alphaCut actual D v g k {before with state:=b.final} := by
 apply NGN_FrameChain.kappa_alpha _ D v before _ g k bytes serialize
 rw [scalar_dictionary]
 exact NGT_CallerInterface.scalar _ D before _ _ false b k reduction

/-- S3 uses the SAME round0 and predecessor transcript. -/
theorem alpha0 {H : Type} (D : aspis_core.Digest32 H) (v : verifier.View)
 (before : transcript.Transcript H) (g k a : aspis_core.field.WideExact)
 (b : NGT_NBL_BlockTrace.Block D before 29#u8 v.round0)
 (reduction : NGT_Reduction.Scalar b.value false a) :
 alphaCut actual D v g k before=foldCut actual D v g k a {before with state:=b.final} := by
 apply NGN_FrameChain.alpha_fold
 rw [scalar_dictionary]
 exact NGT_CallerInterface.scalar _ D before _ _ false b a reduction

/-- S6: no arbitrary rho or arbitrary final state is substituted. -/
theorem rho {H : Type} (D : aspis_core.Digest32 H)
 (sem : r1_semantic.Verified H) (v : verifier.View) (o : Opening H)
 (qs : Array U32 22#usize) (before : transcript.Transcript H) (row : U8)
 (increment : (o.row+1#u8 : Result U8)=ok row)
 (b : NGT_NBL_BlockTrace.Block D before row PreparedScratchReachability.emptyPayload)
 (r : aspis_core.field.QM31) (reduction : NGT_Reduction.K b.value r) :
 rhoCut actual D sem v o qs before=
 powersCut actual D sem v o qs r {before with state:=b.final} := by
 apply NGN_FrameChain.rho_powers _ D sem v o qs before _ row r increment
 rw [rho_dictionary]
 exact NGT_CallerInterface.scalar_k _ D before row _ b r reduction
#print axioms scalar_dictionary
#print axioms rho_dictionary
#print axioms gamma
#print axioms kappa
#print axioms alpha0
#print axioms rho
end AspisR1.NHL_PreparedScalars
