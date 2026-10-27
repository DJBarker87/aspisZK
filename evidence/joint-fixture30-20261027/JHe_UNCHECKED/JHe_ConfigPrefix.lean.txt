import JHe_ConfigFields
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_ConfigPrefix
open Aeneas Aeneas.Std Result DrvC_Installation
abbrev actual (adapter : AdapterRw.Ops) (stage : VTop_Stages.Ops) :=
  DrvC_Installation.currentInstalled (JHe_Configuration.value adapter stage)

theorem slot0 (adapter : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    @(actual adapter stage).op0 = @JGr_Geometry.installed.op0 := by
  unfold actual DrvC_Installation.currentInstalled DrvC_Installation.current
  rw [JHe_ConfigFields.base,JHe_ConfigFields.reserved,JHe_ConfigFields.query,
    JHe_ConfigFields.geometry,JHe_ConfigFields.boundaries,JHe_ConfigFields.std]
  rfl
#print axioms slot0

theorem slot1 (adapter : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    @(actual adapter stage).op1 = @JGr_Geometry.installed.op1 := by
  unfold actual DrvC_Installation.currentInstalled DrvC_Installation.current
  rw [JHe_ConfigFields.base,JHe_ConfigFields.reserved,JHe_ConfigFields.query,
    JHe_ConfigFields.geometry,JHe_ConfigFields.boundaries,JHe_ConfigFields.std]
  rfl
#print axioms slot1

theorem slot2 (adapter : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    @(actual adapter stage).op2 = @JGr_Geometry.installed.op2 := by
  unfold actual DrvC_Installation.currentInstalled DrvC_Installation.current
  rw [JHe_ConfigFields.base,JHe_ConfigFields.reserved,JHe_ConfigFields.query,
    JHe_ConfigFields.geometry,JHe_ConfigFields.boundaries,JHe_ConfigFields.std]
  rfl
#print axioms slot2

theorem slot3 (adapter : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    @(actual adapter stage).op3 = @JGr_Geometry.installed.op3 := by
  unfold actual DrvC_Installation.currentInstalled DrvC_Installation.current
  rw [JHe_ConfigFields.base,JHe_ConfigFields.reserved,JHe_ConfigFields.query,
    JHe_ConfigFields.geometry,JHe_ConfigFields.boundaries,JHe_ConfigFields.std]
  rfl
#print axioms slot3

theorem slot4 (adapter : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    @(actual adapter stage).op4 = @JGr_Geometry.installed.op4 := by
  unfold actual DrvC_Installation.currentInstalled DrvC_Installation.current
  rw [JHe_ConfigFields.base,JHe_ConfigFields.reserved,JHe_ConfigFields.query,
    JHe_ConfigFields.geometry,JHe_ConfigFields.boundaries,JHe_ConfigFields.std]
  rfl
#print axioms slot4

theorem slot5 (adapter : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    @(actual adapter stage).op5 = @JGr_Geometry.installed.op5 := by
  unfold actual DrvC_Installation.currentInstalled DrvC_Installation.current
  rw [JHe_ConfigFields.base,JHe_ConfigFields.reserved,JHe_ConfigFields.query,
    JHe_ConfigFields.geometry,JHe_ConfigFields.boundaries,JHe_ConfigFields.std]
  rfl
#print axioms slot5
end AspisR1.JHe_ConfigPrefix
end
