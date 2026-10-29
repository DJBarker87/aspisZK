import R1Z.PV_OWN_AxiomsAudit
set_option autoImplicit false
namespace R1Z.PV_OWN_FocusedReplay
open PV_OWN_Heap PV_OWN_View PV_OWN_Bytes
/-- Focused replay of the checked interface, not a native consumer restoration. -/
theorem checked_store {T : Type} (codec : Codec T) (m : Memory)
 (cmd : PV_OWN_CheckedStore.Command codec m) :
 View codec (PV_OWN_CheckedStore.execute cmd) cmd.token cmd.offset cmd.value ∧
 Writable (PV_OWN_CheckedStore.execute cmd) cmd.owner cmd.token
  (store cmd.cell cmd.offset codec.width (codec.encode cmd.value)) := by
 constructor
 · exact PV_OWN_CheckedStore.representation cmd
 · exact PV_OWN_Laws.InitWritable codec cmd.token cmd.cell cmd.owner cmd.offset cmd.value m cmd.writable
#print checked_store
#print axioms checked_store
#print axioms PV_OWN_Reserve.complete
#print axioms PV_OWN_Reserve.typed_prefix
#print axioms PV_OWN_CollectorFrame.unread
#print axioms PV_OWN_Containers.zero_capacity
end R1Z.PV_OWN_FocusedReplay
