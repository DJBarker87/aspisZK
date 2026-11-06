import NKD_Gamma
import NKD_Ordinary
import NGT_NBA_SamplerValues
set_option autoImplicit false
namespace AspisR1.NKD_Values
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1ClaimPreparedBridge AspisR1CurrentPreparedClaim.Concrete
/-- The same native gamma output inherits the cohort's canonicality and rank meaning. -/
theorem gamma (block : NGT_NBL_SamplerReplay.Bytes32) (out : aspis_core.field.WideExact)
 (cut : NKD_Gamma.Cut block out) : Canonical (toClaimE out) ∧ GammaRankMeaning block out := by
 obtain ⟨value,call,canonical,rank⟩ := NGT_NBA_SamplerValues.gamma block
 have same : value=out := Result.ok.inj (call.symm.trans (NKD_Gamma.root block out cut))
 subst value
 exact ⟨canonical,rank⟩
/-- A native trace cannot choose a different return than the actual installed cohort. -/
theorem gamma_unique (block : NGT_NBL_SamplerReplay.Bytes32)
 (a b : aspis_core.field.WideExact) (ca : NKD_Gamma.Cut block a) (cb : NKD_Gamma.Cut block b) : a=b :=
 Result.ok.inj ((NKD_Gamma.root block a ca).symm.trans (NKD_Gamma.root block b cb))
#print axioms gamma
#print axioms gamma_unique
#check @gamma
#check @gamma_unique
end AspisR1.NKD_Values
