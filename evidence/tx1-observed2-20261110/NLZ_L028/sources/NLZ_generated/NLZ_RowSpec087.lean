import NLZ_RowSpec137
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLZ_Interface
open Aeneas Aeneas.Std Result AspisR1PublicPreparation AspisR1CurrentCaller NLZ_Resources
structure Observation087 where
 reply : Result NLJ_Prepare.Out
 log : PreparedHashCode.Log
 events : List NLJ_Prepare.Event
 initialHeap : Heap
 finalHeap : Heap
 occurrences : List Occurrence
 proofWindow : Window
 scratchWindow : Window
 logicalOwner : Option Nat
 preparedOwner : Option Nat
/-- Draft ONLY. A fixed cfg and complete resource chain/allocator installation
must replace this schema before (be) admission. No native producer is proved. -/
def RowSpec_087 (cfg : NLJ_Prepare.Configuration)
 (native : NLJ_Prepare.Input Unit → Heap → Window → Observation087) : Prop :=
 ∀ i h window,
 i.proof.val.length=57607 → View h window i.proof.val →
 let o := native i h window
 o.initialHeap = h ∧
 o.proofWindow = window ∧
 NLJ_Prepare.Invocation cfg 12 (NLJ_Prepare.initial i) o.reply o.log o.events ∧
 PreparedHashCode.run (SdkD_PrepareSource.code cfg.base cfg.boundaries cfg.std
  i.digest i.publicValue i.proof i.hash i.scratch) = (o.log,o.reply)
#print RowSpec_087
end AspisR1.NLZ_Interface
end
