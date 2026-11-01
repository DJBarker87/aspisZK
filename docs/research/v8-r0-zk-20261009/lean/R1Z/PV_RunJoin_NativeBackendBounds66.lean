import R1Z.PV_RunJoin_NativeBackendTrace66
import R1Z.PV_RunJoin_NativeBackendConstructor66
import R1Z.PV_RunJoin_BackendC2Frame66
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeBackendBounds66
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63

theorem complete {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (phase : PV_RunJoin_NativeActual63.P base heap box ops runtime world) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box ops runtime world
    ∃ cc1 cc2, phase.val.backend.c1=some cc1 ∧ phase.val.backend.c2=some cc2 ∧
      PV_RunJoin_QueryFillStep64.Domain cc1 ∧ PV_RunJoin_QueryFillStep64.Domain cc2 ∧
      (∃ s,cc1.private_salts=some s ∧ 262144≤s.length) ∧
      (∃ s,cc2.private_salts=some s ∧ 262144≤s.length) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  obtain ⟨initial,columns,d,g,hlen,first,root1,root2,h,hfirst,hsecond,hlift⟩ :=
    PV_RunJoin_NativeBackendTrace66.trace base heap box ops runtime world phase
  have mapErr : @ExternalFuns.op12 (types base) (opsNative base heap box ops runtime world)=
      @ProverRwOuterMapErr.map_err :=
    PV_RunJoin_CaptureBoundary61.selected_mapErr (PV_RunJoin_NativeResidual62.baseTypes base)
      heap box (residual base ops runtime world)
  have pfirst := PV_RunJoin_ResultPost41.success _ _ (.Ok root1,first)
    (PV_RunJoin_BackendConstructor66.c1 mapErr initial columns d) hfirst
  obtain ⟨cc1,hc1,built1⟩ := pfirst
  have psecond := PV_RunJoin_ResultPost41.success _ _ (.Ok root2,phase.val.backend)
    (PV_RunJoin_BackendConstructor66.c2 mapErr first (alloc.vec.Vec.deref h) g) hsecond
  obtain ⟨cc2,hc2,built2⟩ := psecond
  have frame := PV_RunJoin_ResultPost41.success _ _ (.Ok root2,phase.val.backend)
    (PV_RunJoin_BackendC2Frame66.complete first (alloc.vec.Vec.deref h) g) hsecond
  obtain ⟨words1,salts1⟩ := PV_RunJoin_NativeBackendConstructor66.complete base heap box ops runtime world cc1 built1
  obtain ⟨words2,salts2⟩ := PV_RunJoin_NativeBackendConstructor66.complete base heap box ops runtime world cc2 built2
  exact ⟨cc1,cc2,frame.trans hc1,hc2,words1,words2,salts1,salts2⟩

#print axioms complete
end R1Z.PV_RunJoin_NativeBackendBounds66
