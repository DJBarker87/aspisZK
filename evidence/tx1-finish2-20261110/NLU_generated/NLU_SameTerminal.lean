import NLU_ClaimsCanonical
import NLU_InputDomain
import NKQ_AlphaDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU_Terminal
open Aeneas Aeneas.Std Result AspisR1PublicPreparation FIq_Carriers
/-- Source-prefix integration with ACTUAL134/129 outputs, never independently
selected successful values. This conditional support still takes the reviewed
134 native cut; it is not a136 row root or a physical parent certificate. -/
theorem first_calls {H : Type} (native : NJM_RoundsCut.Observations)
 (cut : NJM_RoundsCut.Cut native) (token frame : Nat) (i : NLU.Input H)
 (domain : NLU.InputDomain i) :
 match (PreparedHashCode.run (S1SemanticCode.rounds NJM_RoundJoin.R i.digest i.prefix1 i.transcript)).2 with
 | .ok (.Ok rounds)=>
   match ClaimsUnrolledFinish.claims (NP6_StdModel.calls i.reservation) i.prefix1 with
   | .ok (.Ok claims)=> Packet i.publicValue claims rounds.2.1 i.challenges ∧
     nativeTerminal i.publicValue claims rounds.2.1 i.challenges=
      (IDa_Deployed.boundaries i.reservation).terminal i.publicValue claims rounds.2.1 i.challenges
   | _=>True
 | _=>True := by
 obtain ⟨bytes,pre,parsed,samePrefix⟩:=domain.parsedPrefix
 rw [samePrefix]
 split
 · rename_i rounds returnedRounds
   split
   · rename_i claims returnedClaims
     have alpha:=NKQ_AlphaDomain.source native cut token frame i.digest bytes i.transcript
     rw [parsed] at alpha
     dsimp only at alpha
     rw [returnedRounds] at alpha
     have claimsCanonical:=claims_domain i.reservation bytes pre parsed
     rw [returnedClaims] at claimsCanonical
     have nativeAlpha:=array_to_native rounds.2.1 alpha
     refine ⟨install i.publicValue claims rounds.2.1 i.challenges domain.terminal claimsCanonical nativeAlpha,?_⟩
     exact installed i.publicValue claims rounds.2.1 i.challenges domain.terminal claimsCanonical nativeAlpha
   all_goals trivial
 all_goals trivial
#print axioms first_calls
set_option pp.proofs false in #print first_calls
end AspisR1.NLU_Terminal
end
