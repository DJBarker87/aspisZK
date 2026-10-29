import R1Z.PV_RunJoin_CircleOwnedSelected52
/-! V265 dictionary binding, owned side of the neutral transport. The native
source association uses the accepted structural gate; it is not a machine
proof that the shipped binary equals the reference. No R72 Types import. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CircleBinding62
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]

theorem native_binding (ops : ExternalFuns) (block : Array U8 32#usize)
    (row : aspis_core.r0_transcript.CircleRow) :
    (PV_RunJoin_CircleNeutralSelected52.selected ops).op259 block row = (do
      let point ← PV_AL_CircleNative.nativeCircle block (PV_AL_CircleCarriers.encodeRow row)
      ok (PV_AL_CircleCarriers.decodePoint point)) :=
  (PV_RunJoin_CircleOwnedSelected52.source ops block row).symm.trans
    (PV_AL_CircleSelected.native_source ops block row)

#print axioms native_binding
end R1Z.PV_RunJoin_CircleBinding62
