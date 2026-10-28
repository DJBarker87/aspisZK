import NDO_JHn_R_JHe_ConfigFields
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_CurrentShape
open Aeneas Aeneas.Std Result DrvC_Installation

theorem generic {C : Type} (base : AspisR1CurrentCaller.Ops) (r : Bool)
    (q : Port3_NativeQueryBody.Ops) (g : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls) :
    RowShape_InstalledSlots.verifierOps (Uni_Install.current base r q g) B std=
      Tx1Q_Execution.actual (Op5T_Concrete.current base) r q g B std := by
  rw [Uni_Install.compose_tx1]
  rfl
#print axioms generic

theorem source (adapter : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    DrvC_Installation.currentInstalled (JHe_Configuration.value adapter stage)=
      Tx1Q_Execution.actual (Op5T_Concrete.current (JGp_Allocation.base JGp_Seeds.base)) true
        (SAQ_Decoder.install (JFr_TX2_DotsBinding.ops JGp_Seeds.query))
        (SAQ_Constructor.install () JGp_Seeds.geometry)
        JGe_Boundaries.value (NP6_StdModel.calls (.Ok ())) := by
  unfold DrvC_Installation.currentInstalled DrvC_Installation.current
  rw [JHe_ConfigFields.base,JHe_ConfigFields.reserved,JHe_ConfigFields.query,
    JHe_ConfigFields.geometry,JHe_ConfigFields.boundaries,JHe_ConfigFields.std]
  exact generic _ _ _ _ _ _
#print axioms source
end AspisR1.JHe_CurrentShape
end
