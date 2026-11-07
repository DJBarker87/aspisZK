import NMC_ReachableOrigins
import NMC_RecordAtState
import NKQ_FinishMaskDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMO_ClaimsAtState
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
/-- Canonicality of the SAME stored full Claims value, for every reached
occurrence. The successful source reply is derived from provenance. -/
theorem claims {H : Type} (input : NLU.Input H) (domain : NLU.InputDomain input)
 (s : NLU.State H) (reached : NLU.Reachable input s) (value : Claims)
 (stored : s.machine.locals.claims=some value) : NKQ_MaskCuts.CanonClaims value := by
 obtain ⟨bytes,pre,parsed,prefixEq⟩:=domain.parsedPrefix
 have inputEq:=(NLU.reachable_invariant input s reached).2
 have returned:=(NMC_Origins.reachable input s reached).1 value stored
 rw [inputEq] at returned
 change ClaimsUnrolledFinish.claims (NP6_StdModel.calls input.reservation) input.prefix1=ok (.Ok value) at returned
 have canonical:=NKQ_ClaimsDomain.source input.reservation bytes
 rw [parsed] at canonical
 dsimp only at canonical
 rw [←prefixEq,returned] at canonical
 exact canonical
/-- Canonicality of every SAME stored alpha value; no independently chosen
round carry or completed-array premise enters the caller domain. -/
theorem alpha {H : Type} (native : NJM_RoundsCut.Observations)
 (cut : NJM_RoundsCut.Cut native) (token frame : Nat)
 (input : NLU.Input H) (domain : NLU.InputDomain input)
 (s : NLU.State H) (reached : NLU.Reachable input s) (value : Alpha)
 (stored : s.machine.locals.alpha=some value) : NKQ_MaskCuts.CanonAlpha value := by
 obtain ⟨bytes,pre,parsed,prefixEq⟩:=domain.parsedPrefix
 have inputEq:=(NLU.reachable_invariant input s reached).2
 obtain ⟨running,transcript,origin⟩:=(NMC_Origins.reachable input s reached).2 value stored
 rw [inputEq] at origin
 have returned : (PreparedHashCode.run (S1SemanticCode.rounds NJM_RoundJoin.R input.digest input.prefix1 input.transcript)).2=
  ok (.Ok (running,value,transcript)) := by rw [PreparedHashCode.run_value];exact origin
 have canonical:=NKQ_AlphaDomain.source native cut token frame input.digest bytes input.transcript
 rw [parsed] at canonical
 dsimp only at canonical
 rw [←prefixEq,returned] at canonical
 exact canonical
#print axioms claims
#print axioms alpha
set_option pp.proofs false in #print claims
set_option pp.proofs false in #print alpha
end AspisR1.NMO_ClaimsAtState
end
