import NLR_RowSpec137
import NLJ_PrepareGoal
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_Interface
open Aeneas Aeneas.Std Result AspisR1CurrentCaller AspisR1PublicPreparation
structure Observation087 where
 afterInput : NLJ_Prepare.Input Unit
 afterFrame : ExternalFrame
 reply : Result NLJ_Prepare.Out
 log : PreparedHashCode.Log
 events : List NLJ_Prepare.Event
abbrev Native087 := NLJ_Prepare.Input Unit → ExternalFrame → Observation087
/-- Draft SOURCE/VALUE087 packet, with physical resources still absent. cfg is a FIXED installation to be discharged before
any root; arbitrary Ops/std/boundaries are forbidden at an admitted root.
This declaration proves nothing and supplies no physical producer. Scratch
writeback is in the complete reply, external read-only state in afterFrame;
owned allocations/views/drop and allocator failures require native admission. -/
def RowSpec_087 (cfg : NLJ_Prepare.Configuration) (native : Native087) : Prop :=
 ∀ (i : NLJ_Prepare.Input Unit) (before : ExternalFrame),
 (native i before).afterInput = i ∧
 (native i before).afterFrame = before ∧
 NLJ_Prepare.Invocation cfg 12 (NLJ_Prepare.initial i)
  (native i before).reply (native i before).log (native i before).events ∧
 PreparedHashCode.run (SdkD_PrepareSource.code cfg.base cfg.boundaries cfg.std
  i.digest i.publicValue i.proof i.hash i.scratch) =
  ((native i before).log,(native i before).reply)
#print RowSpec_087
end AspisR1.NLR_Interface
end
