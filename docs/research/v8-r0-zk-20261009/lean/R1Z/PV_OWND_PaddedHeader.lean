import R1Z.PV_OWND_PaddedFold
set_option autoImplicit false
namespace R1Z.PV_OWND_PaddedHeader
open PV_OWNC_Vector PV_OWN_View PV_OWN_Bytes PV_OWND_PaddedFold

theorem length {T : Type} (k : Codec T) (b : Buffer T) (xs : List T)
 (payload : Nat → T → Bytes) (j : Nat) :
 (append k b xs payload j).length=b.length+xs.length := by
 induction xs generalizing b j with
 | nil => simp only [append,List.length_nil,Nat.add_zero]
 | cons v vs ih =>
  rw [append,ih]
  change b.length+1+vs.length=b.length+(vs.length+1)
  omega

theorem identity {T : Type} (k : Codec T) (b : Buffer T) (xs : List T)
 (payload : Nat → T → Bytes) (j : Nat) :
 let a:=append k b xs payload j
 a.capacity=b.capacity ∧ a.owner=b.owner ∧ a.token=b.token ∧
 a.memory.generations=b.memory.generations ∧ a.memory.slots=b.memory.slots ∧
 a.memory.loans=b.memory.loans := by
 induction xs generalizing b j with
 | nil => exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
 | cons v vs ih => exact ih _ _
#print axioms length
#print axioms identity
end R1Z.PV_OWND_PaddedHeader
