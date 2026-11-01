import R1Z.PV_RunJoin_NativeBackendSource66
import R1Z.PV_RunJoin_LiftCoefficients66
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeBackendMatrix66
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63

/-- The actual backend matrix is derived from the two constructor calls and
the stored semantic lift. No hinput or CommonSample premise is used. -/
theorem complete {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (phase : PV_RunJoin_NativeActual63.P base heap box ops runtime world) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box ops runtime world
    phase.val.backend.messages=PV_RunJoin_BackendMatrix58.matrix
      (fun l j => ProverRwDictionaryTower.fromW
        (ProverCommitNativeOps47.embedded ((PV_RunJoin_ActualRun.data phase.val).c l j))) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  obtain ⟨initial,columns,d,g,hlen,domain,first,root1,root2,h,hh,hfirst,hsecond,hlift⟩ :=
    PV_RunJoin_NativeBackendSource66.trace base heap box ops runtime world phase
  let input := PV_RunJoin_BackendRepresentation58.cells initial.messages hlen
  have hinitial : initial.messages=PV_RunJoin_BackendMatrix58.matrix input :=
    (PV_RunJoin_BackendRepresentation58.of_vec initial.messages hlen).symm
  have produced := PV_RunJoin_BackendFullProducer58.complete
    (PV_RunJoin_NativeResidual62.baseTypes base) heap box (residual base ops runtime world)
    initial first phase.val.backend input hinitial columns domain d g (alloc.vec.Vec.deref h) hh
    root1 root2 hfirst hsecond
  rw [PV_RunJoin_BackendRawCoefficients58.matrix] at produced
  have cells : ∀ l,l<29 → ∀ j,j<1024 →
      (PV_RunJoin_ActualRun.data phase.val).c l j=
        PV_RunJoin_BackendRawCoefficients58.coefficients columns domain d (alloc.vec.Vec.deref h) hh g l j := by
    intro l hl j hj
    change PV_RunJoin_LiftCoefficients66.coefficients phase.val.sem.columns l j=_
    exact PV_RunJoin_LiftCoefficients66.complete (PV_RunJoin_NativeResidual62.baseTypes base)
      heap box (residual base ops runtime world) columns domain h hh g d phase.val.sem.columns hlift l j hl hj
  refine produced.trans ?_
  apply PV_RunJoin_BackendRepresentation58.matrix_congr
  intro l hl j hj
  exact congrArg (fun q => ProverRwDictionaryTower.fromW (ProverCommitNativeOps47.embedded q))
    (cells l hl j hj).symm

#print axioms complete
end R1Z.PV_RunJoin_NativeBackendMatrix66
