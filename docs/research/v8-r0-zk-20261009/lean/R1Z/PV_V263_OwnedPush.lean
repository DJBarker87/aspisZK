import R1Z.PV_V263_OwnedDrain
import R1Z.PV_V263_BufferLoop
/-! Source-store specialization of Rust 1.94.1 Vec::push_mut under an existing
reservation. No allocation/failure branch is introduced on this branch. -/
set_option autoImplicit false
namespace R1Z.PV_V263_OwnedPush
open Aeneas Aeneas.Std PV_V263_VectorDrain PV_V263_OwnedDrain

def store {A : Type} (out : Owner A) (a : A)
    (room : out.initialized.values.length+1 ≤ out.initialized.capacity) : Owner A :=
  ⟨PV_V263_BufferLoop.stored out.initialized a room,out.allocation,out.reserved⟩

theorem no_growth {A : Type} (out : Owner A)
    (room : out.initialized.values.length+1 ≤ out.initialized.capacity) :
    out.initialized.values.length≠capacity out.allocation := by
  have h := room.trans out.reserved
  omega

theorem stores {A : Type} (out : Owner A) (a : A)
    (room : out.initialized.values.length+1 ≤ out.initialized.capacity) :
    (store out a room).initialized.values.val=out.initialized.values.val++[a] ∧
    (store out a room).initialized.values.length=out.initialized.values.length+1 ∧
    (store out a room).allocation=out.allocation ∧
    (store out a room).initialized.capacity=out.initialized.capacity ∧
    out.initialized.values.length+1 ≤ Usize.max :=
  ⟨rfl,PV_V263_BufferLoop.stored_length out.initialized a room,rfl,rfl,room.trans out.initialized.bounded⟩

#print axioms store
#print axioms no_growth
#print axioms stores
end R1Z.PV_V263_OwnedPush
