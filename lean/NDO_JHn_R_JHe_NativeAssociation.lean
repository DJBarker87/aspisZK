import NDO_JHn_R_JHe_CurrentAssociation
import NDO_JHn_R_JHe_WriterRestore
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_NativeAssociation
open Aeneas Aeneas.Std Result AspisR1CurrentCaller

/-- The record restoration proof is checked generically before application;
no full concrete record equality is normalized in this proof. -/
theorem source (adapter : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    DrvC_Installation.currentInstalled (JHe_Configuration.value adapter stage)=
      {JGr_Geometry.installed with op16:=Tx1Q_Install.writer} :=
  JHe_WriterRestore.source _ _ (JHe_CurrentAssociation.source adapter stage) rfl
#print axioms source
end AspisR1.JHe_NativeAssociation
end
