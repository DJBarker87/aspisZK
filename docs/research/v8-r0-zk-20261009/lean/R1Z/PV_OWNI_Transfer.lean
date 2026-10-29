import R1Z.PV_OWNI_Stores
import R1Z.PV_OWN_CheckedMove
set_option autoImplicit false
namespace R1Z.PV_OWNI_Transfer
open PV_OWN_Heap PV_OWN_Operations PV_OWNC_Vector
/-- Vec return and IntoIter construction each move the sole owner slot. -/
def moved {T : Type} (b : Buffer T) (dst : Nat) : Buffer T :=
 {b with memory:=move b.owner dst b.token b.cell b.memory,
         cell:={b.cell with owner:=dst},owner:=dst}

theorem valid {T : Type} (k : PV_OWN_View.Codec T) (b : Buffer T) (dst : Nat)
 (h:Valid k b) (empty:b.memory.slots dst=none) (distinct:dst≠b.owner) :
 Valid k (moved b dst) := by
 let command : PV_OWN_CheckedMove.Command b.memory :=
  ⟨b.token,b.cell,b.owner,dst,h.1.1,h.1.2,empty,distinct⟩
 refine ⟨⟨PV_OWN_CheckedMove.transferred command,h.1.2⟩,h.2.1,h.2.2.1,h.2.2.2.1,?_⟩
 intro i hi
 exact h.2.2.2.2 i hi

theorem source_empty {T : Type} (b : Buffer T) (dst : Nat) :
 (moved b dst).memory.slots b.owner=none := by
 simp only [moved,move,ite_true]

theorem bytes {T : Type} (b : Buffer T) (dst : Nat) :
 (moved b dst).cell.contents=b.cell.contents ∧
 (moved b dst).token=b.token ∧ (moved b dst).length=b.length ∧
 (moved b dst).capacity=b.capacity := ⟨rfl,rfl,rfl,rfl⟩
#print axioms valid
#print axioms source_empty
#print axioms bytes
end R1Z.PV_OWNI_Transfer
