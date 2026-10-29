import R1Z.PV_OWND_InitialBytes
set_option autoImplicit false
namespace R1Z.PV_OWND_InitialIdentity
open PV_OWNC_Vector PV_OWNC_PushFold PV_OWN_View PV_OWN_Heap

theorem append_identity {T : Type} (k : Codec T) (b : Buffer T) (xs : List T) :
 (append k b xs).token=b.token ∧ (append k b xs).owner=b.owner ∧
 (append k b xs).memory.generations=b.memory.generations ∧
 (append k b xs).memory.slots=b.memory.slots ∧
 (append k b xs).memory.loans=b.memory.loans := by
 induction xs generalizing b with
 | nil => exact ⟨rfl,rfl,rfl,rfl,rfl⟩
 | cons v vs ih => exact ih _

theorem initial_identity (m : Memory) (t : Token) (owner : Nat) :
 (PV_OWND_InitialBytes.initialized m t owner).token=t ∧
 (PV_OWND_InitialBytes.initialized m t owner).owner=owner ∧
 (PV_OWND_InitialBytes.initialized m t owner).memory.generations=m.generations ∧
 (PV_OWND_InitialBytes.initialized m t owner).memory.slots=m.slots ∧
 (PV_OWND_InitialBytes.initialized m t owner).memory.loans=m.loans := by
 exact append_identity _ _ _
#print axioms append_identity
#print axioms initial_identity
end R1Z.PV_OWND_InitialIdentity
