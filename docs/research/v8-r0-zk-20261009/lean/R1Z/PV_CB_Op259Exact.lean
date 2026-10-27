import R1Z.PV_CB_Op259Funs
import R1Z.PV_CB_Op259Carriers
/-! PREPARED only: fresh extraction and focused type-check are pending. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_Op259Exact
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op259Transport
variable [ExternalTypes]

@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ops with op259 := fun block row => do
    let point ← PV_CB_ShippedOp259.circle_sample block (encodeRow row)
    ok (decodePoint point)}

theorem op259_source (ops : ExternalFuns) (block : Array U8 32#usize)
    (row : aspis_core.r0_transcript.CircleRow) :
    (selected ops).op259 block row = (do
      let point ← PV_CB_ShippedOp259.aspis_r1_cost_probe.sampler.circle_sample
        block (encodeRow row)
      ok (decodePoint point)) := rfl

#print axioms op259_source
end R1Z.PV_CB_Op259Exact
