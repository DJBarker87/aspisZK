import PV_FN_THREAD_f6Interfaces
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6PrefixFrames
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_FN_THREAD_f6Interfaces

/-- The entry argument footprint depends on the carrier and entry store,
not on a callee's installed resolver or native handler. -/
theorem reach {E : Type} (M N : Machine E) (same : M.carrier = N.carrier)
    (x : Entry E) (p : Address) (h : Reach M x p) : Reach N x p := by
  induction h with
  | argument member inside deref =>
    apply Reach.argument member inside
    rw [← same]
    exact deref
  | field suffix prior ih => exact Reach.field suffix ih
  | reference prior cell inside deref ih =>
    apply Reach.reference ih cell inside
    rw [← same]
    exact deref

/-- Caller-cell frame transport does not require a new footprint premise. -/
theorem store_frame {E : Type} (M N : Machine E) (same : M.carrier = N.carrier)
    (x : Entry E) (s : Store Data) (h : StoreFrame M x s) : StoreFrame N x s := by
  refine ⟨h.1,?_⟩
  intro p age outside destination
  exact h.2 p age (fun old => outside (reach M N same x p old)) destination

/-- The same entry footprint transports the complete registry/header/byte
frame. No arbitrary global world frame is introduced. -/
theorem owner_frame {E : Type} (M N : Machine E) (same : M.carrier = N.carrier)
    (x : Entry E) (w : PV_EVHB_OwnerMachine.OWNER) (h : OwnerFrame M x w) : OwnerFrame N x w := by
  intro p age outside
  apply h p age
  intro localIndex fs path old
  exact outside localIndex fs path (reach M N same x _ old)

#print axioms reach
#print axioms store_frame
#print axioms owner_frame
end PV_FN_THREAD_f6PrefixFrames
