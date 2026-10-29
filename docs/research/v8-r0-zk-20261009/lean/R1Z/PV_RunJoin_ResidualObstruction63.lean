import R1Z.PV_RunJoin_CaptureBlocked63
import R1Z.PV_RunJoin_ResidualSuccess63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ResidualObstruction63
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63

/-- Keep every confirmed installation; change only the two uninstalled
residual callbacks. This is a diagnostic family, not the native interpreter. -/
@[reducible] def diagnostic (base : ExternalTypes) (ops : @ExternalFuns (types base)) :
    @ExternalFuns (types base) :=
  letI : ExternalTypes := types base
  {PV_RunJoin_WorkerObstruction63.sparse ops with
    op227 := fun _ _ _ _ => ok (.Ok PV_RunJoin_ActualData59.zeroQ)}

theorem no_capture {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box (diagnostic base ops) runtime world
    ∀ p, ¬PV_RunJoin_ActualProvenance60.Produced p := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box (diagnostic base ops) runtime world
  apply PV_RunJoin_CaptureBlocked63.no_capture (PV_RunJoin_NativeResidual62.baseTypes base)
    heap box (residual base (diagnostic base ops) runtime world)
  intro T F inst count f
  change @ExternalFuns.op257 (types base)
    (opsNative base heap box (diagnostic base ops) runtime world) T F inst 200#usize count f=.div
  rw [PV_RunJoin_NativeFrames63.op257]
  exact PV_RunJoin_WorkerObstruction63.denied ops inst count f

/-- The literal two arbitrary-input existentials do not suffice for capture.
The inputs below are arbitrary values, not success or source-law assumptions. -/
theorem insufficient {S Frame T F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S Frame)
    (world : PV_FXM_ReserveWorld.World S Frame)
    (public1 : @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public (types base))
    (points : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
    (alpha : Array aspis_core.field.QM31 10#usize)
    (challenges : aspis_core.state_only_prefix.r0.Challenges)
    (inst : core.ops.function.Fn F Usize T) (f : F) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box (diagnostic base ops) runtime world
    PV_RunJoin_ResidualSuccess63.Op227Success ∧ PV_RunJoin_ResidualSuccess63.Op257Success ∧
      ¬Nonempty (PV_RunJoin_NativeActual63.P base heap box (diagnostic base ops) runtime world) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box (diagnostic base ops) runtime world
  refine ⟨?_,?_,?_⟩
  · refine ⟨public1,points,alpha,challenges,PV_RunJoin_ActualData59.zeroQ,?_⟩
    change @ExternalFuns.op227 (types base)
      (opsNative base heap box (diagnostic base ops) runtime world) _ _ _ _=_
    rw [PV_RunJoin_NativeFrames63.op227]
    rfl
  · obtain ⟨out,hout⟩ := PV_RunJoin_WorkerObstruction63.some_input ops inst f
    refine ⟨T,F,inst,0#usize,0#usize,f,out,?_⟩
    change @ExternalFuns.op257 (types base)
      (opsNative base heap box (diagnostic base ops) runtime world) T F inst _ _ _=_
    rw [PV_RunJoin_NativeFrames63.op257]
    exact hout
  · rintro ⟨p⟩
    exact no_capture base heap box ops runtime world p.val p.property

#print axioms diagnostic
#print axioms no_capture
#print axioms insufficient
end R1Z.PV_RunJoin_ResidualObstruction63
