import PVO11Borrowed.Funs
import PV_O11_KindView

namespace PV_O11_BorrowedLaw
open Aeneas Aeneas.Std PV_O11_Borrowed

/-- All payload fields remain in the view. No native packed pointer is identified
with this safe reference by this definition. -/
def view {K C M : Type} : Data K C M →
    PV_O11_KindView.View K (Custom K C) (SimpleMessage K M)
  | .Os n => .os n.val
  | .Custom c => .custom c
  | .Simple k => .simple k
  | .SimpleMessage m => .message m

/-- Decode OS codes after the extracted shared-field projection. -/
def getter {K C M : Type} (copyK : core.marker.Copy K)
    (osKind : Int → K) (d : Data K C M) : Result K := do
  let p ← borrowed_kind copyK d
  match p with
  | .Os n => .ok (osKind n.val)
  | .Stored k => .ok k

theorem complete {K C M : Type} (copyK : core.marker.Copy K)
    (osKind : Int → K) (d : Data K C M) :
    getter copyK osKind d = .ok
      (PV_O11_KindView.project osKind Custom.kind SimpleMessage.kind (view d)) := by
  cases d <;> rfl

/-- Shared access leaves the borrowed carrier and the caller's world unchanged
in the reference. Native heap/provenance/world association is still required. -/
def run {K C M W : Type} (copyK : core.marker.Copy K)
    (osKind : Int → K) (d : Data K C M) (w : W) : Result (K × Data K C M × W) := do
  let k ← getter copyK osKind d
  .ok (k,d,w)

theorem frame {K C M W : Type} (copyK : core.marker.Copy K)
    (osKind : Int → K) (d : Data K C M) (w : W) :
    run copyK osKind d w = .ok
      (PV_O11_KindView.project osKind Custom.kind SimpleMessage.kind (view d),d,w) := by
  unfold run
  rw [complete]
  rfl

#print axioms complete
#print axioms frame
end PV_O11_BorrowedLaw
