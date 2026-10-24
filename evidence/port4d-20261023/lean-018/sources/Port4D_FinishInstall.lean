import Port4D_Round
import Port4D_FlushRows
import Port3_Parents
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4D_FinishInstall
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
variable {W CoreError : Type}

def finish (ops : FinishOps W) (v : VTop_Stages.verifier.View)
    (p : VTop_Stages.verifier.Prepared) (a : VTop_Stages.verifier.Accumulator)
    (obs : Option (VTop_Stages.verifier.Phase → Result Unit)) :=
  Port3_QueryInstall.result (Port3_NativeFinishBody.verifier.finish_relation
    (Port4D_Round.native ops) v p a (Port3_QueryInstall.observer obs))

theorem retained_eq (ops : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (obs : Option (VTop_Stages.verifier.Phase → Result Unit)) :
    finish ops v p a obs = Port3_FinishStage.finish ops v p a obs := by
  unfold finish Port3_FinishStage.finish
  rw [Port4D_Round.parent_eq,Port3_FinishStage.parent_eq]

def installed (base : VTop_Stages.Ops) (reserved : Bool)
    (batch : Port3_NativeBatchBody.Ops) (geometry : Port3_NativeGeometryBody.Ops CoreError)
    (query : Port3_NativeQueryBody.Ops) (ops : FinishOps W) : VTop_Stages.Ops :=
  {Port3_Parents.installed base reserved batch geometry query ops with
    op9 := Port4D_FlushRows.flush, op19 := finish ops}

theorem installation (base : VTop_Stages.Ops) (reserved : Bool)
    (batch : Port3_NativeBatchBody.Ops) (geometry : Port3_NativeGeometryBody.Ops CoreError)
    (query : Port3_NativeQueryBody.Ops) (ops : FinishOps W) :
    let dict := installed base reserved batch geometry query ops
    dict.op9 = Port4D_FlushRows.flush ∧ dict.op19 = finish ops := ⟨rfl,rfl⟩

theorem accepted_dot (ops : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (obs : Option (VTop_Stages.verifier.Phase → Result Unit))
    (success : finish ops v p a obs = ok (.Ok ())) :
    ops.dot v.final_message a.weights.deref = ok (.Ok a.rhs) ∧ a.next = 22#usize :=
  Port3_FinishAny.accepted_dot ops v p a obs ((retained_eq ops v p a obs).symm.trans success)

#print axioms retained_eq
#print axioms installation
#print axioms accepted_dot
end AspisR1.Port4D_FinishInstall
end
