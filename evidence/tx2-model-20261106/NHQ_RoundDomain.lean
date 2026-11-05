import NHQ_PacketPorts
set_option autoImplicit false
noncomputable section
namespace NHQ_RoundDomain
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
/-- The first round produces the second round's claim domain on the SAME returned value. -/
theorem output (bytes : Slice U8) (alpha claim out : NE)
 (canonicalAlpha : canonE alpha)
 (returned : NHE_Round.source bytes alpha claim=ok (.Ok out)) : canonE out := by
 unfold NHE_Round.source at returned
 obtain ⟨c0,h0,rest⟩ := Port3_PushFrame.bind_success _ _ _ returned
 obtain ⟨c4,h4,rest⟩ := Port3_PushFrame.bind_success _ _ _ rest
 obtain ⟨lhs,hl,rest⟩ := Port3_PushFrame.bind_success _ _ _ rest
 obtain ⟨rhs,hr,rest⟩ := Port3_PushFrame.bind_success _ _ _ rest
 split at rest
 · cases rest
 · obtain ⟨value,hv,rest⟩ := Port3_PushFrame.bind_success _ _ _ rest
   have same := core.result.Result.Ok.inj (Result.ok.inj rest)
   subst out
   exact NHE_PolynomialDomain.source bytes alpha value canonicalAlpha hv
#print axioms output
end NHQ_RoundDomain
