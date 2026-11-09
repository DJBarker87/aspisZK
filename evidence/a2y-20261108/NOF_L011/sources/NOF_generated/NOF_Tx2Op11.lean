import NOF_CommonConverse
import NNY_ParserAssociation
import NNH_ExactRemainingTypes
set_option autoImplicit false
noncomputable section
namespace AspisR1.NOF_Tx2Op11
open Aeneas Aeneas.Std Result VTop_Stages

/-- Y3: `NNH_ExactRemainingTypes.tx2Op11` exactly as merged. The ACTUAL SDK
op11 is the authenticated TX2 entry over the installed stage: its parser call is
the source parser (NNY_ParserAssociation.source), and its common continuation is
the Y2 converse NOF_CommonConverse.common at the SAME arguments. -/
theorem tx2Op11 : NNH_ExactRemainingTypes.tx2Op11 := by
 unfold NNH_ExactRemainingTypes.tx2Op11
 intro m env err r rep pub proof ck domain success
 obtain ⟨variant,parsed,_⟩ := NNH_AuthCodeOk.entered env pub proof ck success
 have h3 : (NNH_Tx2SlotTransport.stage m env err r).op3 proof = ok (.Ok variant) :=
  (NNY_ParserAssociation.source m env err r proof).trans parsed
 have hc := NOF_CommonConverse.common m env err r rep pub proof ck domain success
 have mk : ∀ ph, (NNH_Tx2SlotTransport.stage m env err r).op13 none ph = ok () := fun _ => rfl
 change verifier.candidate.tx2_authenticated (NNH_Tx2SlotTransport.stage m env err r)
  (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (NNH_CorrectConfiguration.sdk m env err r))
  pub proof ck () none = _
 unfold verifier.candidate.tx2_authenticated
 rw [h3]
 simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,mk]
 exact hc

#print axioms tx2Op11
end AspisR1.NOF_Tx2Op11
end
