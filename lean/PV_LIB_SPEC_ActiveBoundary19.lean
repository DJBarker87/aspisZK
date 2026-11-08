import PV_LIB_SPEC_ActiveNative19
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ActiveBoundary19
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerHeap PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_TlsBound15 (parameters)
open PV_LIB_SPEC_TlsNative15 (cut)

/-- Computed source289 effect, separate from the native physical write. -/
def changed (c : Config) : Config :=
  {c with store := write c.store PV_LIB_SPEC_Entry13.slot.source (some (.boolean true))}

/-- D727 child contraction retains every native answer and the original saved
return action. The source effect is derived by name, never supplied as data. -/
theorem full (nativeCut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (c : Config) (wait : PV_STX2_Native.Waiting Data) (a : Nat) (w : OWNER)
    (r : Reply OWNER Event Data)
    (request : wait.request = PV_LIB_A_F5ClosurePending16.request a PV_LIB_SPEC_Entry13.slot.source)
    (reply : PV_LIB_SPEC_ReachedNative14.answer nativeCut p c
      (PV_LIB_A_ActiveDispatch17.setter a PV_LIB_SPEC_Entry13.slot.source) w = some r) :
    PV_LIB_A_ActiveDispatch17.boundary nativeCut p c wait w =
      some (PV_THR2_ChildBoundary.delivered (runtime p).carrier (changed c) wait r) :=
  PV_LIB_A_ActiveFrames17.full nativeCut p c wait a PV_LIB_SPEC_Entry13.slot.source w r
    (changed c).store request reply (PV_LIB_A_ActiveSetter17.source_write p c.store w)

/-- Concrete successful branch computed from the reached source/physical read.
There is no supplied child-success, allocator-success or post-store hypothesis. -/
theorem successful (stack : PV_LIB_SPEC_PhysicalStack12.Frame) (resources : Resources)
    (c : Config) (wait : PV_STX2_Native.Waiting Data) (a : Nat) (w : OWNER)
    (request : wait.request = PV_LIB_A_F5ClosurePending16.request a PV_LIB_SPEC_Entry13.slot.source)
    (active : PV_LIB_SPEC_TlsBindings13.read PV_LIB_SPEC_Entry13.slot
      (parameters resources) c w = some false) :
    PV_LIB_A_ActiveDispatch17.boundary (cut stack) (parameters resources) c wait w =
      some (PV_THR2_ChildBoundary.delivered (runtime (parameters resources)).carrier
        (changed c) wait ⟨.returned (.ok (.boolean false)),
          PV_LIB_SPEC_CellPhysical13.setByte PV_LIB_SPEC_Entry13.slot w true,[]⟩) := by
  apply full _ _ _ _ a w _ request
  exact PV_LIB_SPEC_ActiveNative19.answer stack resources c w a active

/-- World/event transport for arbitrary replies, including pending, failure,
divergence and fault. It does not discard the native event suffix. -/
theorem effects (p : Parameters) (c : Config) (wait : PV_STX2_Native.Waiting Data)
    (r : Reply OWNER Event Data) :
    (PV_THR2_ChildBoundary.delivered (runtime p).carrier (changed c) wait r).world = r.world ∧
    (PV_THR2_ChildBoundary.delivered (runtime p).carrier (changed c) wait r).events = r.events :=
  PV_THR2_ChildBoundary.effects _ _ _ _

#print axioms changed
#print axioms full
#print axioms successful
#print axioms effects
end PV_LIB_SPEC_ActiveBoundary19
