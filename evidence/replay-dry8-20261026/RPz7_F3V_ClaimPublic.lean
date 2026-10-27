import RPz7_F3V_ClaimDictionary
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_ClaimPublic
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep


theorem same {Hash : Type} (first second : AspisR1PublicPreparation.aspis_core.Digest32 Hash)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified Hash) (y1 : Slice U8)
    (inactive : AspisR1ClaimPreparedBridge.PE)
    (g : Array AspisR1ClaimPreparedBridge.PE 29#usize) (kappa : AspisR1ClaimPreparedBridge.PE) :
    AspisR1ClaimPreparedBridge.claimPublic first sem y1 inactive g kappa=
      AspisR1ClaimPreparedBridge.claimPublic second sem y1 inactive g kappa := by
  unfold AspisR1ClaimPreparedBridge.claimPublic
  rw [F3V_ClaimDictionary.current _ (AspisR1ClaimPreparedBridge.toClaimDigest first)
    (AspisR1ClaimPreparedBridge.toClaimDigest second)]

#print axioms same
end AspisR1.F3V_ClaimPublic
end
