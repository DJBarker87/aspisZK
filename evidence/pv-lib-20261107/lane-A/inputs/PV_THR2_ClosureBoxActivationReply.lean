import PV_THR2_ClosureBoxAllocation
set_option autoImplicit false
noncomputable section
namespace PV_THR2_ClosureBoxActivationReply
open PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
/-- Argument-only bridge into the existing allocation API. The allocation reply
uses ONLY nextActivation, never cells. This coordinate record is never passed
to an interpreter or used in place of a source Store; independence is proved
below. The actual source store and every cell remain untouched. -/
def coordinates (a : Nat) : Store Data := ⟨fun _ => none,a⟩
def reply (resources : Resources) (encode : Encode) (a : Nat) (w : OWNER) :=
  PV_THR2_ClosureBoxAllocation.reply resources encode (coordinates a) w
/-- Symbolic full-reply identity, including every resource branch and world.
The actual store need not be known when installing the native handler. -/
theorem actual (resources : Resources) (encode : Encode) (s : Store Data) (w : OWNER) :
    reply resources encode s.nextActivation w = PV_THR2_ClosureBoxAllocation.reply resources encode s w := rfl
/-- The allocation API is independent of all source cells; this does not relate
or replace interpreter stores. -/
theorem cells_irrelevant (resources : Resources) (encode : Encode) (s t : Store Data) (w : OWNER)
    (same : s.nextActivation = t.nextActivation) :
    PV_THR2_ClosureBoxAllocation.reply resources encode s w =
      PV_THR2_ClosureBoxAllocation.reply resources encode t w := by
  rw [← actual resources encode s w,← actual resources encode t w,same]
#print axioms actual
#print axioms cells_irrelevant
end PV_THR2_ClosureBoxActivationReply
