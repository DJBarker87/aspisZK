import NNE_PhysicalAccepted
set_option autoImplicit false
namespace NNE_Clock
open Aeneas Aeneas.Std AspisR1 S2W_ExtractionBoundary RSL

def image (err : NNE_PhysicalAccepted.PE → ProgramError) (slot : Slot) : Except ProgramError UInt64 :=
 match slot with
 | .Ok n => .ok (UInt64.ofNat n.val)
 | .Err e => .error (err e)

/-- The existing RuntimeClockSlotBinding row, success-conditioned only. -/
def Binding (clock : Except ProgramError UInt64) (bankSlot : UInt64) : Prop :=
 ∀ n, clock = .ok n → n = bankSlot

/-- Both the Ok and error Clock replies are forwarded as the SAME current_slot
argument. No success, monotonicity or retention is inferred from the row. -/
theorem child_argument (err : NNE_PhysicalAccepted.PE → ProgramError)
 (e : S2W_D189Entry.Entry) (p : Program) (data : Slice U8) (env : Env) (slot : Slot)
 (rep : env.clock = image err slot) :
 (NNE_PhysicalAccepted.child2 err e p data env.clock).current_slot = image err slot := rep

theorem success (err : NNE_PhysicalAccepted.PE → ProgramError) (env : Env)
 (slot : Slot) (bankSlot : UInt64) (rep : env.clock = image err slot)
 (binding : Binding env.clock bankSlot) (n : U64) (returned : slot = .Ok n) :
 UInt64.ofNat n.val = bankSlot := by
 apply binding
 rw [rep,returned]
 rfl
#print axioms child_argument
#print axioms success
end NNE_Clock
