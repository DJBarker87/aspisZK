import R1Z.ProverRwP6BodyStore
import R1Z.PV_CB3_Op51Source
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_CB3Flat
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
/-- Source correspondence for an already installed entry; no inventory decrement. -/
theorem selected_bridge (ops : ExternalFuns) (x : aspis_core.field.wide_exact.WideExact) :
    (ProverRwP6BodyStore.selected ops).op51 x =
      (PV_CB3_Op51Source.selected ops).op51 x := by
  change ProverRwP6FlatSource.wide_bytes_flat x = PV_CB3_Op51Source.Raw.wide_bytes_flat x
  rfl
theorem op51_source (ops : ExternalFuns) (x : aspis_core.field.wide_exact.WideExact) :
    (ProverRwP6BodyStore.selected ops).op51 x = PV_CB3_Op51Source.Raw.wide_bytes_flat x :=
  (selected_bridge ops x).trans (PV_CB3_Op51Source.op51_source ops x)
#print axioms selected_bridge
#print axioms op51_source
end R1Z.PV_Join_CB3Flat
