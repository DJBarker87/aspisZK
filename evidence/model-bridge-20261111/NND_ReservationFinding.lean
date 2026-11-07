import NND_064ParseTransport
import NKE_CommonNative
set_option autoImplicit false
noncomputable section
namespace NND_ReservationFinding
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages
/-- Exact differing C06 branch: the native packet's recovered reservation can
be Err while the headline model's Bool is true. This is a representation
alignment obligation, NOT a claim that an actual admitted run violates it. -/
theorem pending_error_differs (weights : Slice aspis_core.field.QM31)
 (width : weights.val.length = 64) (err : NP6_StdModel.ReserveError) :
 NKE_CommonNative.pendingG (.Err err) weights ≠ Port3_NativePendingInstall.source true weights := by
 intro h
 unfold NKE_CommonNative.pendingG at h
 rw [Port3_NativePendingInstall.source,
   Port3_NativePendingInstall.emitted_exact true weights width] at h
 cases h
#print axioms pending_error_differs
end NND_ReservationFinding
