import R1Z.PV_V263_Sequential
/-! Exact old opsNative boundary, with all Result constructors retained.
No V263 association or capture-success premise is installed by these lemmas. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_V263_NativeBoundary
open Aeneas Aeneas.Std ProverRwFull PV_V263_World
open PV_RunJoin_NativeResidual63

/-- The old native dictionary carries no worker post-state. Its full source
Result is precisely that of the still-unbound residual operation. -/
theorem retained {S F T G : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (inst : core.ops.function.Fn G Usize T) (stage count : Usize) (closure : G) :
    @host_work.map (types base) (opsNative base heap box ops runtime world)
      T G inst stage count closure =
    @host_work.map (types base) ops T G inst stage count closure := by
  change @ExternalFuns.op257 (types base) (opsNative base heap box ops runtime world)
    T G inst stage count closure = _
  rw [PV_RunJoin_NativeFrames63.op257]

/-- Even a world-indexed dictionary cannot make a runtime fault a SOURCE
Result under EVH's partial projection. This forbids a total FinishedView; it
neither refutes successful worlds nor the desired existential Nonempty P. -/
theorem no_total_projection {S A : Type} (worker : Q S A)
    (sourceAt : State S → Result A) (w : State S) (e : Fault)
    (faulted : (worker w).outcome = .fault e) :
    ¬ (∀ v, sourceProjection (worker v).outcome = some (sourceAt v)) := by
  intro link
  have h := link w
  rw [faulted] at h
  cases h

/-- The exact Result-producing worker still required by the capture cannot
supply runtime faults through a fabricated source .div or .fail answer. -/
theorem no_total_op257 {S F T G W : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (worldAt : State W → PV_FXM_ReserveWorld.World S F)
    (inst : core.ops.function.Fn G Usize T) (stage count : Usize) (closure : G)
    (worker : Q W (alloc.vec.Vec T)) (w : State W) (e : Fault)
    (faulted : (worker w).outcome = .fault e) :
    ¬ (∀ v, sourceProjection (worker v).outcome = some
      (@host_work.map (types base) (opsNative base heap box ops runtime (worldAt v))
        T G inst stage count closure)) :=
  no_total_projection worker _ w e faulted

#print axioms retained
#print axioms no_total_projection
#print axioms no_total_op257
end R1Z.PV_V263_NativeBoundary
