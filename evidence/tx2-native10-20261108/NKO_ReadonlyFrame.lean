import KMX_CopyMeaning
import NKO_IncomingCuts
set_option autoImplicit false
noncomputable section
namespace NKO_ReadonlyFrame
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages
/-- A byte view of a live region. No concrete57607-cell list is reduced. -/
def view {A : Type} (heap : Nat → A) (base width : Nat) : List A :=
 (List.range width).map (fun i=>heap (base+i))

/-- A native modifies(log) certificate permits arbitrary changes inside the
log object. Its full-object havoc overapproximation is the KMX indexed-write
law. Valid Rust immutable/mutable borrows supply region disjointness. Pointer
identity alone is explicitly insufficient for this theorem. -/
theorem view_frame {A : Type} (written heap : Nat → A)
 (logBase logSize proofBase proofSize : Nat)
 (disjoint : proofBase+proofSize≤logBase ∨ logBase+logSize≤proofBase) :
 view (KMX_CopyMeaning.loop written heap logBase logSize) proofBase proofSize=
 view heap proofBase proofSize := by
 unfold view
 apply List.map_congr_left
 intro i member
 have inside : i<proofSize := List.mem_range.mp member
 exact KMX_CopyMeaning.copy_frame written heap logBase logSize (proofBase+i) (by omega)

/-- Explicit ABI representation binding plus the checked disjoint write frame
identifies every payload byte. These bindings are retained P6 interpretation,
not a new runtime row, and are not inferred from integer addresses. -/
theorem payload (written heap : Nat → U8) (logBase logSize proofBase : Nat)
 (before after : Slice U8)
 (beforeView : before.val=view heap proofBase 57607)
 (afterView : after.val=view (KMX_CopyMeaning.loop written heap logBase logSize) proofBase 57607)
 (disjoint : proofBase+57607≤logBase ∨ logBase+logSize≤proofBase) : after=before := by
 apply Subtype.ext
 rw [afterView,view_frame written heap logBase logSize proofBase 57607 disjoint,beforeView]

/-- The fully checked native memory frame can replace the fourteen byte-window
projections, once its SAME-call representation binding is installed. This is
auxiliary: a Cut declaration or a metadata probe alone earns no native credit. -/
theorem required_windows (before after : Slice U8) (same : after=before) :
 (∀ block,NKO_HalfProofWindows.Window before after block) ∧
 NKO_HalfProofWindows.Tail before after := by
 subst after
 exact ⟨fun _ _ _=>rfl,fun _ _=>rfl⟩
#print axioms view_frame
#print axioms payload
#print axioms required_windows
end NKO_ReadonlyFrame
