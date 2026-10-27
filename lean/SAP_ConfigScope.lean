import SAP_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAP_ConfigScope
open DrvC_Installation

theorem dictionary_fields {F C : Type} (c : Configuration F C) :
    (SAP_Install.configuration c).adapter=(DrvC_FirstConstants.configuration c).adapter ∧
    (SAP_Install.configuration c).currentBase=(DrvC_FirstConstants.configuration c).currentBase ∧
    (SAP_Install.configuration c).stageBase=(DrvC_FirstConstants.configuration c).stageBase ∧
    (SAP_Install.configuration c).finish=(DrvC_FirstConstants.configuration c).finish ∧
    (SAP_Install.configuration c).reserved=(DrvC_FirstConstants.configuration c).reserved ∧
    (SAP_Install.configuration c).query=(DrvC_FirstConstants.configuration c).query ∧
    (SAP_Install.configuration c).geometry=(DrvC_FirstConstants.configuration c).geometry ∧
    (SAP_Install.configuration c).std=(DrvC_FirstConstants.configuration c).std := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem install_idempotent (B : AspisR1PublicPreparation.FinishModel.Boundaries) :
    F3M_CircleSource.install (F3M_CircleSource.install B)=F3M_CircleSource.install B := rfl

theorem exact_scope {F C : Type} (c : Configuration F C) :
    SAP_Install.configuration c=DrvC_FirstConstants.configuration c ↔
      c.boundaries.circle=F3M_CircleSource.source := by
  constructor
  · intro same
    exact (congrArg (fun r : Configuration F C=>r.boundaries.circle) same).symm
  · exact SAP_Install.unchanged_if_installed c

#print axioms dictionary_fields
#print axioms install_idempotent
#print axioms exact_scope
end AspisR1.SAP_ConfigScope
end
