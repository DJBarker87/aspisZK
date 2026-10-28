import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem AllocFresh (prim : Request → S → Outcome E (Option Nat) × S) (r : Request) (w : State S X)
 (p : Nat) (s : S) (adequate:AllocatorAdequate prim r w) (h:prim r w.allocator=(.ok (some p),s)) :
 p≠0 ∧ r.alignment>0 ∧ p%r.alignment=0 := by
 obtain ⟨a,b,c,_⟩:=adequate p s h
 exact ⟨a,b,c⟩
#print axioms AllocFresh
end R1Z.PV_OWN_Laws
