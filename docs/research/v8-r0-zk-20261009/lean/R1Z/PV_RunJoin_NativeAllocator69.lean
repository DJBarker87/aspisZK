import R1Z.PV_RunJoin_NativeActual63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeAllocator69
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63

theorem source {T S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) (Allocator : Type)
    (v : alloc.vec.Vec T) (n : Usize) :
    letI : ExternalTypes := types base
    @alloc.vec.Vec.try_reserve_exact (types base) (opsNative base heap box ops runtime world) T Allocator v n=
      ok (PV_FXM_ReserveSelected.returned runtime.encode
        (PV_RunJoin_AllocatorWorld63.execute runtime world v n).returned,v) := by
  letI : ExternalTypes := types base
  change @ExternalFuns.op32 (types base) (opsNative base heap box ops runtime world) T Allocator v n=_
  rw [PV_RunJoin_NativeFrames63.op32]
  rfl

theorem success_iff {T S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) (Allocator : Type)
    (v : alloc.vec.Vec T) (n : Usize) :
    letI : ExternalTypes := types base
    @alloc.vec.Vec.try_reserve_exact (types base) (opsNative base heap box ops runtime world) T Allocator v n=
      ok (.Ok (),v) ↔ (PV_RunJoin_AllocatorWorld63.execute runtime world v n).returned=.ok () := by
  letI : ExternalTypes := types base
  rw [source]
  cases (PV_RunJoin_AllocatorWorld63.execute runtime world v n).returned with
  | ok u => cases u;exact ⟨fun _ => rfl,fun _ => rfl⟩
  | error e => simp only [PV_FXM_ReserveSelected.returned,Result.ok.injEq,Prod.mk.injEq,
      reduceCtorEq,and_true]

/-- The actual source continuation reads the callback selected at this world.
No success, allocator adequacy or post-world identity is assumed. -/
theorem bind {T S F A : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) (Allocator : Type)
    (v : alloc.vec.Vec T) (n : Usize)
    (next : letI : ExternalTypes := types base
      core.result.Result Unit alloc.collections.TryReserveError → alloc.vec.Vec T → Result A) :
    letI : ExternalTypes := types base
    (do let (r,v') ← @alloc.vec.Vec.try_reserve_exact (types base)
          (opsNative base heap box ops runtime world) T Allocator v n
        next r v')=
      next (PV_FXM_ReserveSelected.returned runtime.encode
        (PV_RunJoin_AllocatorWorld63.execute runtime world v n).returned) v := by
  letI : ExternalTypes := types base
  rw [source]
  rfl

#print axioms source
#print axioms success_iff
#print axioms bind
end R1Z.PV_RunJoin_NativeAllocator69
