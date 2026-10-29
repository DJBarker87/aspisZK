import R1Z.PV_OWN_CheckedAlloc
import R1Z.PV_OWND_LegacySource
set_option autoImplicit false
namespace R1Z.PV_OWND_AllocationBuffer
open PV_OWN_Heap PV_OWN_Operations PV_OWN_View PV_OWNC_Vector PV_W_Threading
/-- The buffer header comes from the actual allocation post-world, not an
assumed initialized-prefix premise. Its length starts at zero. -/
def buffer {T : Type} (k : Codec T) (capacity owner : Nat) (m : Memory)
 (t : Token) (default : T) : Buffer T :=
 ⟨m,t,owner,emptyCell (capacity*k.width) k.alignment owner,0,capacity,fun _=>default⟩

theorem valid {S X E T : Type} (k : Codec T) (capacity owner : Nat) (default : T)
 (prim : Request → S → Outcome E (Option Nat) × S) (w : State S X) (p : Nat) (s : S)
 (h:prim ⟨capacity*k.width,k.alignment⟩ w.allocator=(.ok (some p),s))
 (loans:NoLoans w.memory ⟨p,w.memory.generations p+1⟩) :
 PV_OWNC_Vector.Valid k (buffer k capacity owner
  (allocate prim ⟨capacity*k.width,k.alignment⟩ owner w).world.memory
  ⟨p,w.memory.generations p+1⟩ default) := by
 unfold PV_OWNC_Vector.Valid buffer
 refine ⟨⟨?_,?_⟩,rfl,rfl,Nat.zero_le _,?_⟩
 · simp [Owned,Live,allocate,emit,h,put,emptyCell]
 · simpa only [NoLoans,allocate,emit,h] using loans
 · intro i hi
   omega
attribute [local irreducible] buffer
#print axioms valid
end R1Z.PV_OWND_AllocationBuffer
