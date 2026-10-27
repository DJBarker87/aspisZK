import R1Z.PV_Op223_P6Bridge
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Op223_Source
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
/-- The applied candidate's actual host compressor callback. Other rows retain
    their dictionary selection and their existing proof obligations. -/
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ops with op223 := PV_Op223_Applied.prover_shared.compress_tagged_tuple}

/-- Complete Result source binding, universally quantified over raw inputs. -/
theorem op223_source (ops : ExternalFuns) :
    ExternalFuns.op223 (selected ops) =
      PV_Op223_Applied.prover_shared.compress_tagged_tuple := rfl

/-- Exact V164 source hypothesis for this applied candidate dictionary. -/
theorem P_source_p6 (ops : ExternalFuns) :
    (selected ops).op223 =
      @ProverRwP6CompressSource.compress _
        (PV_CurrentScaleInstall.selected (selected ops)) :=
  PV_Op223_P6Bridge.reference (selected ops)
#print axioms op223_source
#print axioms P_source_p6
end R1Z.PV_Op223_Source
