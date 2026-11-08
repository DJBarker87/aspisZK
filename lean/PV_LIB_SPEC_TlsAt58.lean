import PV_LIB_SPEC_Tls277Request15
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_TlsAt58
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Context initial)
open PV_LIB_SPEC_TlsNative15 (cut reference)

def at58 : Execution := PV_LIB_SPEC_Tls277Request15.after PV_LIB_SPEC_TlsDelivery15.store55 5
  reference PV_LIB_SPEC_TlsOriginal15.parents PV_LIB_SPEC_Entry14.state []
  PV_LIB_SPEC_TlsAt54.at54.issued [PV_LIB_SPEC_TlsAt55.origin]

theorem original58 (stack : PV_LIB_SPEC_PhysicalStack12.Frame) :
    PV_LIB_SPEC_ReachedNative14.run (cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters 58
      (initial PV_LIB_SPEC_Entry14.input) = at58 := by
  rw [show 58=55+3 from rfl,PV_LIB_SPEC_Original14.run_add,PV_LIB_SPEC_TlsAt55.original55]
  apply PV_LIB_SPEC_Tls277Request15.request
  simp [PV_LIB_SPEC_TlsDelivery15.store55,PV_STX2_Store.write]

/-- Same entry Pre and SAME history now includes its first actual native
answer. No physical frame, f295/f454 or later resource success is inferred. -/
theorem first_native (stack : PV_LIB_SPEC_PhysicalStack12.Frame) :
    (PV_LIB_SPEC_ReachedNative14.run (cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters 58
      (initial PV_LIB_SPEC_Entry14.input)).consumed = [PV_LIB_SPEC_TlsAt55.origin] := by
  rw [original58]; rfl

theorem world58 (stack : PV_LIB_SPEC_PhysicalStack12.Frame) :
    (PV_LIB_SPEC_ReachedNative14.run (cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters 58
      (initial PV_LIB_SPEC_Entry14.input)).state.current.world = PV_LIB_SPEC_Entry14.state := by
  rw [original58]; rfl

#print axioms at58
#print axioms original58
#print axioms first_native
#print axioms world58
end PV_LIB_SPEC_TlsAt58
