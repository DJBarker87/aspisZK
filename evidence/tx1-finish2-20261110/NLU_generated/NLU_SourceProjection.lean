import NLU_FoldProjection
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- Full Result and chronological source equality, including rejected/abort
prefixes. Only the source projection of the proposed owner fold is proved;
this is deliberately not a native RowSpec136 theorem. -/
theorem source_projection {H : Type} (input : Input H) :
 (digestLog (fold (NLC_Finish.fuel (NLC_Finish.initial input)) (initial input)).events,
  eraseReply (fold (NLC_Finish.fuel (NLC_Finish.initial input)) (initial input)).reply)=
 PreparedHashCode.run (S1SemanticCode.finish NJM_RoundJoin.R
  (IDa_Deployed.boundaries input.reservation) input.digest input.publicValue
  input.prefix1 input.transcript input.challenges none) := by
 exact (fold_projection _ (initial input)).trans (NLI_Source.finishSourceEquality input)
#print axioms source_projection
set_option pp.proofs false in #print source_projection
end AspisR1.NLU
end
