import NNY_ParserAssociation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNY_AuthenticatedPrefix
open Aeneas Aeneas.Std Result VTop_Stages
/-- Complete parser/mark prefix of the actual SDK op11. The common call stays
literally in the result; no common equality or success is assumed. -/
theorem source (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (pub proof ck : Slice U8) :
 (NNH_CorrectConfiguration.sdk m env err r).op11
  (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (NNH_CorrectConfiguration.sdk m env err r))
  pub proof ck () none =
 (do
  let result ← NLE_ParseInstall.parse proof
  match result with
  | .Err e => ok (.Err e)
  | .Ok _ => verifier.candidate.tx2_common (NNH_Tx2SlotTransport.stage m env err r)
    (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (NNH_CorrectConfiguration.sdk m env err r))
    pub proof ck () none) := by
 change verifier.candidate.tx2_authenticated (NNH_Tx2SlotTransport.stage m env err r) _ _ _ _ _ _ = _
 unfold verifier.candidate.tx2_authenticated
 rw [NNY_ParserAssociation.source]
 cases parsed : NLE_ParseInstall.parse proof with
 | fail e => rfl
 | div => rfl
 | ok result => cases result <;> rfl
#print axioms source
end AspisR1.NNY_AuthenticatedPrefix
end
