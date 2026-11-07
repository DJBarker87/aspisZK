import NLZ_Resources
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLZ_Interface
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLZ_Resources
structure Observation137 where
 reply : Result (NLJ_Observed.Out Unit)
 log : PreparedHashCode.Log
 events : List NLJ_Observed.Event
 initialHeap : Heap
 finalHeap : Heap
 occurrences : List Occurrence
 inputWindow : Window
 claimsOwner : Option Nat
/-- Draft interface, intentionally NOT presented as full-strength under (be).
Resource chain, child footprints, abort cleanup and claims ownership are
mandatory named obligations still missing below; none can be discharged by
this value projection. It is forbidden as a child packet until strengthened. -/
def RowSpec_137 (native : NLJ_Observed.Input Unit → Heap → Window → Observation137) : Prop :=
 ∀ i h window,
 i.bytes.val.length=13831 → View h window i.bytes.val →
 let o := native i h window
 o.initialHeap = h ∧
 o.inputWindow = window ∧
 NLJ_Observed.Invocation 6 (NLJ_Observed.initial i) o.reply o.log o.events ∧
 PreparedHashCode.run (S1SemanticCode.verify
  (S1SemanticCode.finish NJM_RoundJoin.R (IDa_Deployed.boundaries i.reservation))
  i.digest i.publicValue i.bytes i.hash none) = (o.log,o.reply)
#print RowSpec_137
end AspisR1.NLZ_Interface
end
