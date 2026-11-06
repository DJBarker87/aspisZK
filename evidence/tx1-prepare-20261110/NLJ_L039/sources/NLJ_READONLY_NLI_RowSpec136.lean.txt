import NLC_BridgeGoal
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_Interface
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
/-- Semantic observation of the native parent, with immutable input frame,
complete outer and inner Result, entered occurrence order and chronological
oracle effects. A producer must fix this function to the frozen native cuts;
an arbitrary function satisfying the spec is not a row certificate. -/
structure Observation (H : Type) where
 afterInput : Input H
 reply : Result (Out H)
 log : PreparedHashCode.Log
 events : List Event
/-- Parent-facing TX1:136 obligation. Every input is the SAME input of the
native producer. It includes rejection/fail/div prefixes, never only success.
The producer's source association is reviewed under P6/D188; proving this
Prop for an unrelated function is not native credit. -/
def RowSpec_136 {H : Type} (native : Input H → Observation H) : Prop :=
 ∀ input,
  (native input).afterInput = input ∧
  InitializedInvocation (fuel (initial input)) (initial input)
   (native input).reply (native input).log (native input).events ∧
  PreparedHashCode.run (S1SemanticCode.finish NJM_RoundJoin.R
   (IDa_Deployed.boundaries input.reservation) input.digest input.publicValue
   input.prefix1 input.transcript input.challenges none) =
   ((native input).log, (native input).reply)
#print RowSpec_136
end AspisR1.NLI_Interface
end
