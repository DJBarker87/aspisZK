import R1Z.PV_RunJoin_ResidualObstruction63
import R1Z.PV_RunJoin_OracleBridge38
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BridgeObstruction73
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63

/-- A diagnostic dictionary only: retain the supplied terminal exactly and
make the actual commitment worker diverge. This is not a deployed dictionary. -/
def diagnostic (base : ExternalTypes) (ops : @ExternalFuns (types base))
    (terminal : @PV_RunJoin_OracleBridge38.Terminal (types base)) :
    @ExternalFuns (types base) :=
  letI : ExternalTypes := types base
  {PV_RunJoin_WorkerObstruction63.sparse ops with op227 := terminal}

/-- The full callback equality holds at every input, including any reached
claims. No terminal totality or replacement terminal value is used. -/
theorem callback {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (terminal : @PV_RunJoin_OracleBridge38.Terminal (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) :
    @ExternalFuns.op227 (types base)
      (opsNative base heap box (diagnostic base ops terminal) runtime world)=terminal := by
  rw [PV_RunJoin_NativeFrames63.op227]
  rfl

/-- The same dictionary has no successful capture, despite the complete
op227 callback law. This isolates the independent op257 obligation. -/
theorem no_capture {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (terminal : @PV_RunJoin_OracleBridge38.Terminal (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) :
    ¬Nonempty (PV_RunJoin_NativeActual63.P base heap box
      (diagnostic base ops terminal) runtime world) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box (diagnostic base ops terminal) runtime world
  rintro ⟨p⟩
  apply PV_RunJoin_CaptureBlocked63.no_capture (PV_RunJoin_NativeResidual62.baseTypes base)
    heap box (residual base (diagnostic base ops terminal) runtime world) ?_ p.val p.property
  intro T C inst count f
  change @ExternalFuns.op257 (types base)
    (opsNative base heap box (diagnostic base ops terminal) runtime world)
      T C inst 200#usize count f=.div
  rw [PV_RunJoin_NativeFrames63.op257]
  exact PV_RunJoin_WorkerObstruction63.denied ops inst count f

/-- Even the globally quantified exact runjoin callback bridge cannot imply
non-emptiness uniformly over the current residual dictionary family. This is
an interface counterexample, not a counterexample to deployed execution. -/
theorem insufficient {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (terminal : @PV_RunJoin_OracleBridge38.Terminal (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) :
    ¬(∀ candidate : @ExternalFuns (types base),
      @ExternalFuns.op227 (types base) (opsNative base heap box candidate runtime world)=terminal →
      Nonempty (PV_RunJoin_NativeActual63.P base heap box candidate runtime world)) := by
  intro all
  exact no_capture base heap box ops terminal runtime world
    (all (diagnostic base ops terminal) (callback base heap box ops terminal runtime world))

#print axioms diagnostic
#print axioms callback
#print axioms no_capture
#print axioms insufficient
end R1Z.PV_RunJoin_BridgeObstruction73
