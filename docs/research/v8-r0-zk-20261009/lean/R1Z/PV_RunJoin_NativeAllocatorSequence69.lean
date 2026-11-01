import R1Z.PV_RunJoin_NativeAllocator69
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeAllocatorSequence69
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63

/-- Actual immutable native dictionary, two consecutive source callbacks.
The second request and its size may depend on the first returned status.
The post-world is computed explicitly; replacing the second fixed-world
callback by that post-world requires the stated equality of returned statuses. -/
theorem complete {T U S F A : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) (Allocator : Type)
    (v : alloc.vec.Vec T) (n : Usize)
    (u : letI : ExternalTypes := types base
      core.result.Result Unit alloc.collections.TryReserveError → alloc.vec.Vec U)
    (m : letI : ExternalTypes := types base
      core.result.Result Unit alloc.collections.TryReserveError → Usize)
    (caller : letI : ExternalTypes := types base
      core.result.Result Unit alloc.collections.TryReserveError →
      core.result.Result Unit alloc.collections.TryReserveError → Result A)
    (compatible : letI : ExternalTypes := types base
      let first := PV_RunJoin_AllocatorWorld63.execute runtime world v n
      let status := PV_FXM_ReserveSelected.returned runtime.encode first.returned
      PV_FXM_ReserveSelected.returned runtime.encode
        (PV_RunJoin_AllocatorWorld63.execute runtime world (u status) (m status)).returned=
      PV_FXM_ReserveSelected.returned runtime.encode
        (PV_RunJoin_AllocatorWorld63.execute runtime first.world (u status) (m status)).returned) :
    letI : ExternalTypes := types base
    (do let (r,_) ← @alloc.vec.Vec.try_reserve_exact (types base)
          (opsNative base heap box ops runtime world) T Allocator v n
        let (s,_) ← @alloc.vec.Vec.try_reserve_exact (types base)
          (opsNative base heap box ops runtime world) U Allocator (u r) (m r)
        caller r s)=
      let first := PV_RunJoin_AllocatorWorld63.execute runtime world v n
      let status := PV_FXM_ReserveSelected.returned runtime.encode first.returned
      let second := PV_RunJoin_AllocatorWorld63.execute runtime first.world (u status) (m status)
      caller status (PV_FXM_ReserveSelected.returned runtime.encode second.returned) := by
  letI : ExternalTypes := types base
  rw [PV_RunJoin_NativeAllocator69.source]
  simp only [bind_tc_ok,Aeneas.Std.uncurry]
  rw [PV_RunJoin_NativeAllocator69.source]
  simp only [bind_tc_ok,Aeneas.Std.uncurry]
  exact congrArg (caller _) compatible

#print axioms complete
end R1Z.PV_RunJoin_NativeAllocatorSequence69
