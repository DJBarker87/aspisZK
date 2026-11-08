import NNS_LibraryContext
set_option autoImplicit false
noncomputable section
namespace NNS_PortLaw241
open RSL RSL.TX2_241 NMS_R2Replay241 NNS_Fold241

/-- This is the fallback's actual function, not NNH_064Install.f064. -/
abbrev f064 := fun pub proof ck env => NMX_R7_Verify241.verify (pub,proof,ck) env

/-- Root0 and tx2auth are unused by the replay when its verifier is explicit;
its debug/error carrier stays fixed. -/
theorem replay_same (ch : NMX_R4_Authentication.Choices)
 (R0 : Bytes → Bytes → Prop) (w : Bytes → Bytes → Bytes → Spec (Except V0.VErr Unit))
 (a : Args) :
 replay L (TAS.lib V0 R0 w) (NMX_R6_Validation.validate ch) NMX_R7_Verify241.verify a =
 replay L V0 (NMX_R6_Validation.validate ch) NMX_R7_Verify241.verify a :=
 NNS_LibraryContext.replay L V0 R0 w (NMX_R6_Validation.validate ch) NMX_R7_Verify241.verify a

/-- Complete restatement of the fallback row only, with exactly the supplied
064 and 242 premises. The represented native branch is a separate obligation. -/
theorem root (ch : NMX_R4_Authentication.Choices)
 (R0 : Bytes → Bytes → Prop) (w : Bytes → Bytes → Bytes → Spec (Except V0.VErr Unit))
 (h064 : TAS.Refines064 V0 f064 R0 w)
 (h242 : TX2_242.RowSpec_242 L D (NMX_R6_Validation.validate ch)) :
 RowSpec_241 L D (TAS.lib V0 R0 w) (NMX_R7_Port241.stage2 ch) := by
 intro a env domain
 have law := NNS_Fold241.fold ch f064 R0 w h064 h242 a domain
 change NMS_R2Refine.Refines
  (replay L (TAS.lib V0 R0 w) (NMX_R6_Validation.validate ch) NMX_R7_Verify241.verify a) _ at law
 rw [replay_same] at law
 exact law env _ (NMX_R7_PortLaw241.replay_member ch a env)

#print axioms replay_same
#print axioms root
end NNS_PortLaw241
