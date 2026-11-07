import NMC_EraseBind
import NLU_SlotFrames
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMC_Origins
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
/-- Internal provenance of the actual stored local, derived from source
steps. These are NOT hypotheses allowed at a136 root. -/
def ClaimsOrigin {H : Type} (s : NLC_Finish.State H) : Prop :=
 ∀ claims,s.locals.claims=some claims→
 (IDa_Deployed.boundaries s.input.reservation).claims s.input.prefix1=ok (.Ok claims)
def AlphaOrigin {H : Type} (s : NLC_Finish.State H) : Prop :=
 ∀ alpha,s.locals.alpha=some alpha→∃ running transcript,
 PreparedHashCode.erase (S1SemanticCode.rounds NJM_RoundJoin.R s.input.digest s.input.prefix1 s.input.transcript)=
 ok (.Ok (running,alpha,transcript))
theorem initial_claims {H : Type} (input : Input H) : ClaimsOrigin (NLC_Finish.initial input) := by
 intro claims stored;cases stored
theorem initial_alpha {H : Type} (input : Input H) : AlphaOrigin (NLC_Finish.initial input) := by
 intro alpha stored;cases stored
/-- After a non-writing occurrence, this is the SAME stored child Result,
transported through the proved source input and local frames. -/
theorem claims_preserved {H : Type} (s after : NLC_Finish.State H)
 (major : Major s) (origin : ClaimsOrigin s) (notClaims : s.next≠.claims)
 (head : (PreparedHashCode.run (NLC_Finish.step s)).2=ok (.inr after)) : ClaimsOrigin after := by
 have input:=NLC_Finish.source_input_frame s after head
 have locals:=(NLU_Slots.source_frame s after major head).1 notClaims
 intro claims stored
 rw [locals] at stored
 simpa only [input] using origin claims stored
theorem alpha_preserved {H : Type} (s after : NLC_Finish.State H)
 (major : Major s) (origin : AlphaOrigin s) (notRounds : s.next≠.rounds)
 (head : (PreparedHashCode.run (NLC_Finish.step s)).2=ok (.inr after)) : AlphaOrigin after := by
 have input:=NLC_Finish.source_input_frame s after head
 have locals:=(NLU_Slots.source_frame s after major head).2 notRounds
 intro alpha stored
 rw [locals] at stored
 simpa only [input] using origin alpha stored
#print axioms initial_claims
#print axioms initial_alpha
#print axioms claims_preserved
#print axioms alpha_preserved
end AspisR1.NMC_Origins
end
