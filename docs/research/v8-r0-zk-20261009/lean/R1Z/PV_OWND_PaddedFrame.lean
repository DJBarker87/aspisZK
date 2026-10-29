import R1Z.PV_OWND_PaddedFold
set_option autoImplicit false
namespace R1Z.PV_OWND_PaddedFrame
open PV_OWNC_Vector PV_OWN_View PV_OWN_Bytes PV_OWN_Heap PV_OWND_PaddedFold

theorem header {T : Type} (k : Codec T) (b : Buffer T) (xs : List T)
 (payload : Nat → T → Bytes) (j : Nat) :
 let c:=(append k b xs payload j).cell
 c.size=b.cell.size ∧ c.alignment=b.cell.alignment ∧ c.capacity=b.cell.capacity ∧
 c.owner=b.cell.owner ∧ c.live=b.cell.live := by
 induction xs generalizing b j with
 | nil => exact ⟨rfl,rfl,rfl,rfl,rfl⟩
 | cons v vs ih => exact ih _ _

theorem other {T : Type} (k : Codec T) (b : Buffer T) (xs : List T)
 (payload : Nat → T → Bytes) (j address : Nat) (hne:address≠b.token.address) :
 (append k b xs payload j).memory.heap address=b.memory.heap address := by
 induction xs generalizing b j with
 | nil => rfl
 | cons v vs ih =>
  rw [append,ih]
  · exact put_other _ _ _ _ hne
  · exact hne
#print axioms header
#print axioms other
end R1Z.PV_OWND_PaddedFrame
