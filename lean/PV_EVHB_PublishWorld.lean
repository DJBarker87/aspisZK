import PV_EVHB_PublishInstall
set_option autoImplicit false
noncomputable section
namespace PV_EVHB_PublishWorld
open Aeneas Aeneas.Std ProverRwFull PV_EVH_Runtime PV_EVH_AllocatorWorld
open PV_RJ4IDB (Bytes NativeEvent)
variable [ExternalTypes] [ExternalFuns]

/-- Capacity allocation and typed callbacks are part of the reached publication
body. Other native leaves retain explicit effectful computations. -/
def run (variant : transport.Variant) (p : prover.Publication)
    (c : PV_EVHB_PublishInstall.Leaves) (frames : PV_EVH_RuntimeOperators.Frames)
    (allocator : Allocator) (encode : AllocationEvent → Bytes)
    (element : Type → Layout) (maxBytes owner : Nat)
    (overflowDiagnostics oomDiagnostics : List NativeEvent) :=
  PV_EVHB_PublishCompact.run variant p
    (PV_EVHB_PublishInstall.install c frames allocator encode element maxBytes owner
      overflowDiagnostics oomDiagnostics)

theorem source_view (variant : transport.Variant) (p : prover.Publication)
    (c : PV_EVHB_PublishInstall.Leaves) (frames : PV_EVH_RuntimeOperators.Frames)
    (allocator : Allocator) (encode : AllocationEvent → Bytes)
    (element : Type → Layout) (maxBytes owner : Nat)
    (overflowDiagnostics oomDiagnostics : List NativeEvent)
    (hc : PV_EVHB_PublishInstall.Compatible c)
    (hf : PV_EVH_RuntimeOperators.Compatible frames)
    (selected : PV_EVH_OperatorFrames.Selection (inferInstance : ExternalFuns)) :
    PartialView (run variant p c frames allocator encode element maxBytes owner
      overflowDiagnostics oomDiagnostics) (prover.publish_compact variant p) :=
  PV_EVHB_PublishCompact.run_fixed variant p _
    (PV_EVHB_PublishInstall.install_view c frames allocator encode element maxBytes owner
      overflowDiagnostics oomDiagnostics hc hf selected) selected

/-- Allocation denial stops the FULL publication body before MAGIC/serialization.
The public-count prefix, allocator mutation, errno and denial diagnostics survive.
No successful-only guard is placed on this result. -/
theorem initial_denied (variant : transport.Variant) (p : prover.Publication)
    (c : PV_EVHB_PublishInstall.Leaves) (frames : PV_EVH_RuntimeOperators.Frames)
    (allocator : Allocator) (encode : AllocationEvent → Bytes)
    (element : Type → Layout) (maxBytes owner : Nat)
    (overflowDiagnostics oomDiagnostics : List NativeEvent)
    (state : State) (count : Usize) (layout : Layout)
    (hc : (c.op242_OPEN state).outcome = .returned (.ok count))
    (hl : PV_EVH_CapacityWorld.layoutFor (element Std.U8).size (element Std.U8).align
      maxBytes count = .ok layout)
    (hz : layout.size ≠ 0)
    (ha : (allocator (c.op242_OPEN state).state layout).answer = .denied) :
    let allocation := PV_EVH_CapacityWorld.withCapacity allocator encode
      (element Std.U8).size (element Std.U8).align maxBytes owner
      overflowDiagnostics oomDiagnostics Std.U8 count (c.op242_OPEN state).state
    run variant p c frames allocator encode element maxBytes owner
      overflowDiagnostics oomDiagnostics state =
      ⟨.fault (.allocationDenied layout),allocation.state,
        (c.op242_OPEN state).events ++ allocation.events⟩ := by
  have denied := PV_EVH_CapacityWorld.allocator_failure allocator encode
    (element Std.U8).size (element Std.U8).align maxBytes owner
    overflowDiagnostics oomDiagnostics Std.U8 count layout (c.op242_OPEN state).state hl hz ha
  simp only [run,PV_EVHB_PublishCompact.run,PV_EVHB_PublishInstall.install,
    Bind.bind,PV_EVH_Runtime.bind,hc,denied.1]

#print axioms source_view
#print axioms initial_denied
end PV_EVHB_PublishWorld
