import R1Z.PV_OWNB_Padding
set_option autoImplicit false
namespace R1Z.PV_OWNB_PaddingStore
open PV_OWN_Heap PV_OWN_Bytes PV_OWNB_Padding
/-- A relation over actual initialized bytes, without equating padding to None. -/
def Represents (required : Bytes) (width : Nat) (c : Cell) (start : Nat) : Prop :=
 Fits c start width ∧ Agrees required (fun i => c.contents (start+i))
/-- Native typed moves may copy arbitrary padding; the proof needs active bytes only. -/
theorem written (required actual : Bytes) (width : Nat) (c : Cell) (start : Nat)
 (fits:Fits c start width) (bounded:∀ i b, required i=some b → i<width)
 (h:Agrees required actual) : Represents required width (store c start width actual) start := by
 refine ⟨fits,?_⟩
 intro i b hi
 change overwrite c.contents start width actual (start+i)=some b
 rw [inside _ _ _ _ _ (bounded i b hi)]
 exact h i b hi

theorem canonical (required : Bytes) (width : Nat) (c : Cell) (start : Nat)
 (fits:Fits c start width) (bounded:∀ i b, required i=some b → i<width) :
 Represents required width (store c start width required) start :=
 written required required width c start fits bounded (PV_OWNB_Padding.refl required)

attribute [irreducible] Represents
#print axioms written
#print axioms canonical
end R1Z.PV_OWNB_PaddingStore
