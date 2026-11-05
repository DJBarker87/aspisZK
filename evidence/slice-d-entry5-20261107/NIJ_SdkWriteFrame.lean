import NHJ_SdkBorrowPacket
set_option autoImplicit false
namespace NIJ_SdkWriteFrame
open AspisR1.S2Trust

theorem byte {F : Type} (s : Heap F) (g : Guard) (i : Nat) (v : UInt8) :
 ((writeAt s g i v).payload g.cell).contents i=v := by
 simp only [writeAt,put,ite_true]

theorem other_byte {F : Type} (s : Heap F) (g : Guard) (i j : Nat) (v : UInt8)
 (different : j≠i) :
 ((writeAt s g i v).payload g.cell).contents j=(s.payload g.cell).contents j := by
 simp only [writeAt,put,ite_true,different,ite_false]

theorem other_cell {F : Type} (s : Heap F) (g : Guard) (i cell : Nat) (v : UInt8)
 (different : cell≠g.cell) : (writeAt s g i v).payload cell=s.payload cell := by
 simp only [writeAt,put,different,ite_false]

theorem descriptor {F : Type} (s : Heap F) (g : Guard) (i cell : Nat) (v : UInt8) :
 ((writeAt s g i v).payload cell).descriptor=(s.payload cell).descriptor := by
 by_cases same : cell=g.cell <;> simp [writeAt,put,same]

theorem frame {F : Type} (s : Heap F) (g : Guard) (i : Nat) (v : UInt8) :
 (writeAt s g i v).accounts=s.accounts ∧
 (writeAt s g i v).counter=s.counter ∧
 (writeAt s g i v).guards=s.guards ∧
 (writeAt s g i v).ambient=s.ambient ∧
 (writeAt s g i v).ownerLive=s.ownerLive ∧
 (writeAt s g i v).allocated=s.allocated ∧
 (writeAt s g i v).external=s.external := by
 exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem valid {F : Type} (s : Heap F) (g : Guard) (i : Nat) (v : UInt8)
 (before : Valid s) : Valid (writeAt s g i v) := by
 rcases before with ⟨pairs,bounds,live,owners⟩
 refine ⟨pairs,bounds,?_,owners⟩
 intro h member
 obtain ⟨allocated,desc⟩:=live h member
 exact ⟨allocated,desc.trans (descriptor s g i h.cell v).symm⟩

#print axioms byte
#print axioms other_byte
#print axioms other_cell
#print axioms descriptor
#print axioms frame
#print axioms valid
end NIJ_SdkWriteFrame
