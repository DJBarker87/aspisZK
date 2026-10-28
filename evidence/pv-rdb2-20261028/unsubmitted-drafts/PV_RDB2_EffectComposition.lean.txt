import R1Z.PV_RDB2_ResultEffects
import R1Z.PV_RDB2_PointerBridge
import R1Z.PV_RDB2_CtCopy

/-! Representation transport composes with effectful callbacks without
discarding their failure-world evidence or divergence prefix. -/
namespace R1Z.PV_RDB2_EffectComposition
set_option autoImplicit false
open Aeneas Aeneas.Std Result PV_RDB2_ResultEffects

def oldAfterCast {World Buffer : Type}
    (finish : Step World (PV_RDB2_NonNull.Wrapped × Buffer)) :
    Step World (PV_RDB2_NonNull.Wrapped × Buffer) :=
  bind finish (fun pair => pureStep (PV_RDB2_NonNull.historicalCast pair.1,pair.2))

def deployedAfterCast {World Buffer : Type}
    (finish : Step World (PV_RDB2_NonNull.Wrapped × Buffer)) :
    Step World (PV_RDB2_NonNull.Wrapped × Buffer) :=
  bind finish (fun pair => pureStep (PV_RDB2_NonNull.deployedCast pair.1,pair.2))

theorem complete {World Buffer : Type}
    (finish : Step World (PV_RDB2_NonNull.Wrapped × Buffer)) :
    oldAfterCast finish = deployedAfterCast finish := rfl

theorem error_world {World Buffer : Type}
    (finish : Step World (PV_RDB2_NonNull.Wrapped × Buffer))
    (before after : World) (error : Error) (h : finish before = (.fail error,after)) :
    deployedAfterCast finish before = (.fail error,after) :=
  failure_frame finish _ before after error h

theorem divergence_world {World Buffer : Type}
    (finish : Step World (PV_RDB2_NonNull.Wrapped × Buffer))
    (before after : World) (h : finish before = (.div,after)) :
    deployedAfterCast finish before = (.div,after) := divergence_prefix finish _ before after h

theorem changed_buffer {World Buffer : Type}
    (finish : Step World (PV_RDB2_NonNull.Wrapped × Buffer))
    (before after : World) (pointer : PV_RDB2_NonNull.Wrapped) (buffer : Buffer)
    (h : finish before = (ok (pointer,buffer),after)) :
    deployedAfterCast finish before = (ok (PV_RDB2_NonNull.deployedCast pointer,buffer),after) := by
  simp only [deployedAfterCast,PV_RDB2_ResultEffects.bind,h,pureStep]

#print axioms complete
#print axioms error_world
#print axioms divergence_world
#print axioms changed_buffer
end R1Z.PV_RDB2_EffectComposition
