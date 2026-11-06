import NJJ_Common
import NHV_PendingPacket
set_option autoImplicit false
noncomputable section
namespace NJR_ReservationSites
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

/-- Resume's actual ZERO64 filled occurrence with the SAME universally
quantified Reservation. Both error and success are retained; no success clause
constrains r. The native arguments/ownership carrier are NJJ_K066--069. -/
theorem resume_filled (r : NP6_StdModel.Reservation) :
 NJC_FilledClause.native r = CheckpointBytes3Allocation.filled
 (NJC_FilledClause.reserved r) 64#usize
 (⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩ : aspis_core.field.QM31) :=
 NJC_FilledClause.source r

/-- At the pending constructor's literal source site, the quantified value is
passed directly to the source body. No independent return or runtime Bool is
introduced. This is source-site installation, not native allocator semantics. -/
theorem pending (r : NP6_StdModel.Reservation) (a : verifier.Accumulator)
 (width : a.weights.val.length=64) :
 NJJ_Common.pending r a.weights.deref =
 match r with
 | .Ok () => ok (.Ok (NFW_QueryResume.pending a))
 | .Err _ => ok (.Err .Allocation) := by
 unfold NJJ_Common.pending
 rw [NHV_PendingPacket.source _ a width]
 cases r with
 | Ok unit => cases unit; rfl
 | Err e => rfl

/-- The two sites remain independent data, including either failure arm.
This theorem does not claim that their private allocator states coincide. -/
theorem pending_error (e : NP6_StdModel.ReserveError) (a : verifier.Accumulator)
 (width : a.weights.val.length=64) :
 NJJ_Common.pending (.Err e) a.weights.deref=ok (.Err .Allocation) := by
 exact pending (.Err e) a width

#print axioms resume_filled
#print axioms pending
#print axioms pending_error
end NJR_ReservationSites
