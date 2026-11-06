import NLI_SourceComparison
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Source
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
open PreparedHashCode (Code run)
/-- The explicit NLC open source goal, at the original input and with the
complete Result and chronological digest effects. This is not a native row. -/
theorem finishSourceEquality {H : Type} (input : Input H) :
 NLC_Goals.FinishSourceEquality input := by
 unfold NLC_Goals.FinishSourceEquality
 change run (fold 34 {input:=input,locals:={},next:=.rounds}) = _
 exact (NLI_Source.rounds input {}).trans (suffix_eq_finish input)
/-- NLC's internally produced initialized occurrence fold now has the
adopted finish Result/log. No native invocation hypothesis is introduced. -/
theorem initialized_finish {H : Type} (input : Input H) :
 ∃ out log events, InitializedInvocation (fuel (initial input)) (initial input) out log events ∧
 run (S1SemanticCode.finish NJM_RoundJoin.R (IDa_Deployed.boundaries input.reservation)
 input.digest input.publicValue input.prefix1 input.transcript input.challenges none) = (log,out) := by
 obtain ⟨out,log,events,cuts,folded⟩:=NLC_Finish.initial_fold input
 exact ⟨out,log,events,cuts,(finishSourceEquality input).symm.trans folded⟩
#print axioms finishSourceEquality
#print axioms initialized_finish
#print finishSourceEquality
#print initialized_finish
end AspisR1.NLI_Source
end
