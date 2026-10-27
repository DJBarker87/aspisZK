import JHf_ReconstructionConfiguration
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHf_RealPool
open Aeneas Aeneas.Std Result DrvC_Installation

theorem source {C : Type} (c : Configuration FIo_Install.W C) (err : C) :
    (sdk (JHf_ReconstructionConfiguration.value c err)).op37 JHd_RequestCarrier.actual.pool_program=
      ok JHb_Programs.pool := by
  rw [JHd_RequestCarrier.pool]
  rfl
#print axioms source
end AspisR1.JHf_RealPool
end
