import SAG_ScaleConfig
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAG_ScaleScope
open Aeneas Aeneas.Std Result

/-- Scope of specialization: only the two native scalar primitive slots are
selected; all source operands and remaining body slots are retained. -/
theorem retained {W : Type} (ops : AspisR1Stage2.Stage2Finish.FinishOps W) :
    (SAG_StageScale.install ops).field = ops.field ∧
    (SAG_StageScale.install ops).add = ops.add ∧
    (SAG_StageScale.install ops).polynomial = ops.polynomial ∧
    (SAG_StageScale.install ops).newWeights = ops.newWeights ∧
    (SAG_StageScale.install ops).pair = ops.pair ∧
    (SAG_StageScale.install ops).dot = ops.dot := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem compatible {F C : Type} (c : DrvC_Installation.Configuration F C)
    (r : NP6_StdModel.Reservation)
    (quarter : c.finish.quarter = ok 536870912#u32)
    (multiply : c.finish.mulM = SAG_StageScale.mulM) :
    SAG_ScaleConfig.configuration c r = Rc3_Install.configuration c r := by
  have installed := (SAG_ScaleConfig.installed_eq c.finish).mpr ⟨quarter,multiply⟩
  unfold SAG_ScaleConfig.configuration SAG_ScaleConfig.select
  rw [installed]

#print axioms retained
#print axioms compatible
end AspisR1.SAG_ScaleScope
end
