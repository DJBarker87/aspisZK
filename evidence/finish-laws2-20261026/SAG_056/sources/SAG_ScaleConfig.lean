import SAG_StageScale
import Rc3_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAG_ScaleConfig
open Aeneas Aeneas.Std Result

def select {F C : Type} (c : DrvC_Installation.Configuration F C) :=
  {c with finish := SAG_StageScale.install c.finish}

def configuration {F C : Type} (c : DrvC_Installation.Configuration F C)
    (r : NP6_StdModel.Reservation) := Rc3_Install.configuration (select c) r

theorem finish {F C : Type} (c : DrvC_Installation.Configuration F C)
    (r : NP6_StdModel.Reservation) :
    (configuration c r).finish = SAG_StageScale.install c.finish := rfl

theorem installed_eq {W : Type} (ops : AspisR1Stage2.Stage2Finish.FinishOps W) :
    SAG_StageScale.install ops = ops ↔
      ops.quarter = ok 536870912#u32 ∧ ops.mulM = SAG_StageScale.mulM := by
  constructor
  · intro h
    exact ⟨(congrArg (fun x => x.quarter) h).symm,
      (congrArg (fun x => x.mulM) h).symm⟩
  · rintro ⟨hq,hm⟩
    unfold SAG_StageScale.install
    rw [←hq,←hm]

#print axioms finish
#print axioms installed_eq
end AspisR1.SAG_ScaleConfig
end
