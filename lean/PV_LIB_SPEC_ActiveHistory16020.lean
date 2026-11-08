import PV_LIB_SPEC_Active27720
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ActiveHistory16020
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution)
open PV_LIB_SPEC_EntryWorld18 (Entry)
open PV_LIB_A_F5FullEntry16 (activation parents)
open PV_LIB_SPEC_ActiveDelivery20 (stored)
open PV_LIB_SPEC_TlsNative15 (reference)
open PV_LIB_SPEC_ActiveAdoption19 (history)

def at159 (e : Entry) (a : Nat) : Execution :=
  PV_LIB_SPEC_Active27720.before stored activation parents PV_LIB_SPEC_Entry13.slot.source e.world []
    (history e a 156).issued (history e a 156).consumed

theorem original159 (e : Entry) (a : Nat) : history e a 159 = at159 e a := by
  let q := history e a 156
  have eq : q = PV_LIB_SPEC_F1Arithmetic14.stage stored activation parents
      (PV_THR2_F170.live.body.drop 14) e.world [] q.issued q.consumed := by
    refine PV_LIB_A_F170Return16.execution_ext q
      (PV_LIB_SPEC_F1Arithmetic14.stage stored activation parents
        (PV_THR2_F170.live.body.drop 14) e.world [] q.issued q.consumed) ?_ rfl rfl
    change (history e a 156).state = _
    rw [PV_LIB_SPEC_ActiveConsume20.original]
    rfl
  change PV_LIB_A_ActiveEnvironment17.run _ _ (156+3) _ = _
  rw [PV_LIB_A_ActiveEnvironment17.run_add]
  change PV_LIB_A_ActiveEnvironment17.run _ _ 3 q = _
  calc
    _ = PV_LIB_A_ActiveEnvironment17.run _ _ 3
      (PV_LIB_SPEC_F1Arithmetic14.stage stored activation parents
        (PV_THR2_F170.live.body.drop 14) e.world [] q.issued q.consumed) := congrArg _ eq
    _ = at159 e a := PV_LIB_SPEC_Active277Issue20.run _ _ stored activation reference parents
      e.world [] q.issued q.consumed (write_same _ _ _)

/-- The next full native consumption is on the original adopted history. -/
theorem original160 (e : Entry) (a : Nat) :
    history e a 160 =
      ⟨PV_LIB_SPEC_Active27720.out stored activation parents PV_LIB_SPEC_Entry13.slot.source e.world [],
        (at159 e a).issued,
        PV_LIB_SPEC_Active27720.origin stored activation PV_LIB_SPEC_Entry13.slot.source
          (history e a 156).consumed :: (history e a 156).consumed⟩ := by
  change PV_LIB_A_ActiveEnvironment17.run _ _ (159+1) _ = _
  rw [PV_LIB_A_ActiveEnvironment17.run_add]
  change PV_LIB_A_ActiveEnvironment17.step _ _ (history e a 159) = _
  rw [original159]
  exact PV_LIB_SPEC_Active27720.consume _ stored activation parents PV_LIB_SPEC_Entry13.slot.source
    e.world [] _ _

#print axioms at159
#print axioms original159
#print axioms original160
end PV_LIB_SPEC_ActiveHistory16020
