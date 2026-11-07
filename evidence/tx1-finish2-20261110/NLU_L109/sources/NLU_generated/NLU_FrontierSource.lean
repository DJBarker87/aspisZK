import NLU_Frontier
import NLU_SourceProjection
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU_Frontier
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
theorem initialized_frontier {H : Type} (input : NLU.Input H) :
 NLU.Invariant (run (NLC_Finish.fuel (NLC_Finish.initial input)) (NLU.initial input)).frontier ∧
 (run (NLC_Finish.fuel (NLC_Finish.initial input)) (NLU.initial input)).frontier.machine.input=input :=
 NLU.reachable_invariant input _ (reached input _ (NLU.initial input) .initial)
/-- Whole source projection of one invocation, now retaining a valid last
entered state on all abort prefixes. Native heap/child-prefix interpretation
is explicitly still unproved. -/
theorem source {H : Type} (input : NLU.Input H) :
 (NLU.digestLog (run (NLC_Finish.fuel (NLC_Finish.initial input)) (NLU.initial input)).summary.events,
 NLU.eraseReply (run (NLC_Finish.fuel (NLC_Finish.initial input)) (NLU.initial input)).summary.reply)=
 PreparedHashCode.run (S1SemanticCode.finish NJM_RoundJoin.R (IDa_Deployed.boundaries input.reservation)
 input.digest input.publicValue input.prefix1 input.transcript input.challenges none) := by
 simp only [summary]
 exact NLU.source_projection input
#print axioms initialized_frontier
#print axioms source
set_option pp.proofs false in #print source
end AspisR1.NLU_Frontier
end
