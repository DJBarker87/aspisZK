import NHT_PacketOps
set_option autoImplicit false
noncomputable section
namespace NHV_PendingPacket
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
/-- The initialized rows are the SAME resumed weight coordinates, through the
existing nominal ports; this supplies no independent pending witness. -/
theorem raw_same (a : verifier.Accumulator) :
 Port3_PendingInstall.raw a.weights.deref=
 S7Kani3CallerTrace.initialRaw (NFW_QueryResume.rowWeights a) := by
 rw [Port3_PendingInstall.initial_raw]
 rfl

/-- Actual emitted constructor, including allocation rejection, instantiated on
SAME resumed weights. Native one-step association is separate evidence. -/
theorem source (reserved : Bool) (a : verifier.Accumulator)
 (width : a.weights.val.length=64) :
 Port3_NativePendingInstall.source reserved a.weights.deref =
 if reserved then ok (.Ok (NFW_QueryResume.pending a))
 else ok (.Err VTop_Stages.verifier.Error.Allocation) := by
 rw [Port3_NativePendingInstall.reference_eq reserved a.weights.deref width,
   Port3_PendingInstall.pending_exact,raw_same]
 cases reserved <;> rfl

/-- A returned constructor value supplies NHT's exact pending field. Success
is used only to identify that actual returned value, never to force allocation. -/
theorem returned (reserved : Bool) (a : verifier.Accumulator)
 (width : a.weights.val.length=64) (pending : verifier.BatchedWeights)
 (call : Port3_NativePendingInstall.source reserved a.weights.deref=ok (.Ok pending)) :
 pending=NFW_QueryResume.pending a := by
 rw [source reserved a width] at call
 cases reserved with
 | false => cases call
 | true => exact (core.result.Result.Ok.inj (Result.ok.inj call)).symm
#print axioms raw_same
#print axioms source
#print axioms returned
end NHV_PendingPacket
