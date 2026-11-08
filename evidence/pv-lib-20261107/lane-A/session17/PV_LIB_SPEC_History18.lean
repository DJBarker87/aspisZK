import PV_LIB_SPEC_TlsWorld18_5
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_History18
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution initial)
open PV_LIB_SPEC_EntryWorld18 (Entry frame concrete input)

def history (entry : Entry) (activation n : Nat) : Execution :=
  PV_LIB_SPEC_ReachedNative14.run (PV_LIB_SPEC_TlsNative15.cut (frame entry activation))
    PV_LIB_SPEC_ReachedEnvironment14.parameters n (initial (input entry.world))

theorem original85 (entry : Entry) (activation : Nat) :
    history entry activation 85 = PV_LIB_SPEC_World18_Tls85Data16.at85 entry :=
  PV_LIB_SPEC_World18_TlsAt85.original85 entry (frame entry activation)

theorem concrete85 (activation : Nat) :
    history concrete activation 85 = PV_LIB_SPEC_World18_Tls85Data16.at85 concrete :=
  original85 concrete activation

theorem world85 (entry : Entry) (activation : Nat) :
    (history entry activation 85).state.current.world = entry.world := by
  rw [original85]
  rfl

theorem replies85 (entry : Entry) (activation : Nat) :
    (history entry activation 85).consumed =
      [PV_LIB_SPEC_Tls85Data16.origin,PV_LIB_SPEC_Tls68Data16.origin,
        PV_LIB_SPEC_Tls64Data16.origin,PV_LIB_SPEC_Tls59Data15.origin,PV_LIB_SPEC_TlsAt55.origin] := by
  rw [original85]
  change PV_LIB_SPEC_Tls85Data16.origin ::
    (PV_LIB_SPEC_World18_TlsAt84.at84 entry).consumed = _
  rw [PV_LIB_SPEC_World18_TlsAt84.consumed84,PV_LIB_SPEC_World18_TlsAt75.consumed75]
  change PV_LIB_SPEC_Tls85Data16.origin :: PV_LIB_SPEC_Tls68Data16.origin ::
    (PV_LIB_SPEC_World18_TlsAt67.at67 entry).consumed = _
  rw [PV_LIB_SPEC_World18_TlsAt67.consumed67]

/-- SPEC-C16 numeric separation check for the concrete initial stack grant.
This does not assert fresh-allocation validity for arbitrary reached owners. -/
theorem scheduled_heap_away (statement size address : Nat)
    (selected : PV_LIB_SPEC_SuccessSchedule12.pointer statement size = some address) :
    concrete.stackGrant.base+concrete.stackGrant.size ≤ address := by
  unfold PV_LIB_SPEC_SuccessSchedule12.pointer at selected
  split at selected
  · cases selected; decide
  · split at selected
    · cases selected; decide
    · split at selected
      · cases selected; decide
      · split at selected
        · cases selected; decide
        · split at selected
          · cases selected; decide
          · cases selected

theorem rejected_overlap :
    ¬ PV_OWN2_FreshAllocation.RangeDisjoint 3584 1024 4096 48 := by
  unfold PV_OWN2_FreshAllocation.RangeDisjoint
  omega

#print axioms history
#print axioms original85
#print axioms concrete85
#print axioms world85
#print axioms replies85
#print axioms scheduled_heap_away
#print axioms rejected_overlap
end PV_LIB_SPEC_History18
