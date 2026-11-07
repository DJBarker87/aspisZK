import NMC_WindowModels
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMC_Partial
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NMC_Window NMC_Models
/-- The one-iteration invariant is on the actual partially initialized
buffer, never on an independently supplied completed array. -/
def Prefix {n : Nat} (buffer : Partial n) (count : Nat) : Prop :=
 buffer.initialized=count ∧ count≤n ∧
 ∀ j,(j.val < count→∃ value,buffer.cells j=some value) ∧ (count ≤ j.val→buffer.cells j=none)
theorem write_frame {n : Nat} (before : Partial n) (i j : Fin n) (value : NLC_Finish.Q)
 (different : j≠i) : (writePartial before i value).cells j=before.cells j := by
 simp only [writePartial,if_neg different]
theorem write_cell {n : Nat} (before : Partial n) (i : Fin n) (value : NLC_Finish.Q) :
 (writePartial before i value).cells i=some value := by simp [writePartial]
theorem write_identity {n : Nat} (before : Partial n) (i : Fin n) (value : NLC_Finish.Q) :
 (writePartial before i value).identity=before.identity := rfl
/-- Exact prefix progression, including every untouched uninitialized cell. -/
theorem advance {n : Nat} (before : Partial n) (i : Fin n) (value : NLC_Finish.Q)
 (ready : Prefix before i.val) : Prefix (writePartial before i value) (i.val+1) := by
 refine ⟨rfl,by omega,?_⟩
 intro j
 constructor
 · intro written
   by_cases same : j=i
   · cases same;exact ⟨value,write_cell before i value⟩
   · have earlier : j.val < i.val := by
      have neq : j.val≠i.val := fun h=>same (Fin.ext h)
      omega
     obtain ⟨old,stored⟩:=(ready.2.2 j).1 earlier
     exact ⟨old,(write_frame before i j value same).trans stored⟩
 · intro future
   have different : j≠i := by intro h;cases h;omega
   exact (write_frame before i j value different).trans ((ready.2.2 j).2 (by omega))
#print axioms write_frame
#print axioms write_cell
#print axioms write_identity
#print axioms advance
end AspisR1.NMC_Partial
end
