import NJR_ReservationSites
set_option autoImplicit false
noncomputable section
namespace NJR_ReservationRaw
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
abbrev Row := Port3_NativePendingBody.Row

def mapError {T : Type} : core.result.Result T FIo_Native.aspis_core.r0.Error →
 core.result.Result T Unit
 | .Ok v => .Ok v
 | .Err _ => .Err ()

/-- Actual emitted generic filled, with the standard fixed-array Copy and the
SAME quantified reservation installed at this source site. -/
def filled (r : NP6_StdModel.Reservation) (n : Usize) (value : Row) :=
 letI:=FIo_Install.allocation r
 FIo_FieldBridge.map mapError (FIo_Native.aspis_core.r0.heap.filled
  (Array.Insts.CoreMarkerCopy 4#usize core.marker.CopyU64) n value)

theorem zero (r : NP6_StdModel.Reservation) (n : Usize) :
 filled r n (Array.repeat 4#usize 0#u64)=
 Port3_NativePendingInstall.heap (NJC_FilledClause.reserved r) n
  (Array.repeat 4#usize 0#u64) := by
 unfold filled
 rw [NHI_FilledModel.contents r _ n _ (by rfl),Port3_NativePendingInstall.heap_exact]
 cases r with
 | Err e => rfl
 | Ok unit => cases unit; rfl

/-- The concrete native-emitted allocator call replaces the old Bool heap at
its ACTUAL occurrence inside the pending body. No allocation-success
hypothesis or endpoint Result is supplied; both reserve arms are universal. -/
theorem pending (r : NP6_StdModel.Reservation) (weights : Slice aspis_core.field.QM31) :
 Port3_QueryInstall.result (Port3_NativePendingBody.extracted (filled r) weights)=
 NJJ_Common.pending r weights := by
 unfold NJJ_Common.pending Port3_NativePendingInstall.source
 unfold Port3_NativePendingBody.extracted
 dsimp only
 rw [zero]

#print axioms zero
#print axioms pending
end NJR_ReservationRaw
