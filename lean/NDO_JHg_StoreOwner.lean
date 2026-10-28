import NDO_JHg_World
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHg_StoreOwner
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry

theorem all (store : Store) (key address : Nat) (saved : alloc.vec.Vec U8) :
    (commit store key saved address).owner=(store address).owner := by
  unfold commit put
  by_cases same : address=key
  · subst address
    rw [if_pos rfl]
  · rw [if_neg same]
#print axioms all
end AspisR1.JHg_StoreOwner
end
