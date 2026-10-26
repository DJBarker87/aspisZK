import CPS_EntryFlags
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPS_ParentBoundary
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames MultiproofConeCanonical CPR_DataPersistence

def next (t u : Bool) : Prop := t = false ∧ u = true
def ordinary (_ : Bool) (_ : Unit) : Prop := True
def image (bytes : Bytes) (_ : Bool) (_ : Unit) : Image := ⟨bytes,1⟩
def status (_ : Bool) : Bool := false
def loader (bytes : Bytes) (_ : Bool) (_ : Unit) : Option Bytes := some bytes

/-- A genuine adjacent, ordinary load after a failed parent observes the
pre-parent image. Native CPI acceptance cannot change final parent status. -/
theorem law (old saved : Bytes) :
    TwoTransactionLaw next ordinary (image old) (image saved) status (loader old) := by
  intro t u adjacent key eligible
  rfl

/-- Preserve BOTH exact accepted native wrapper equations on their original
witnesses while extending them with a non-vacuous law-satisfying failed parent.
This is conditional on that supplied pair; it does not construct a full crypto
inhabitant or claim an association of these annotations with deployment. -/
theorem accepted_pair {A : Type}
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (e1 e2 : Entry) (id : S2W_ExtractionBoundary.Program)
    (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (state1 state2 final1 final2 : A) (saved : alloc.vec.Vec U8)
    (post1 post2 : Heap (Nat → Record))
    (accepted1 : first n1 copy allocator e1 id data1 state1 = ok (.Ok (saved,post1,final1)))
    (accepted2 : second n2 allocator e2 id data2 slot state2 = ok (.Ok (post2,final2))) :
    let old := bytesOf (e2.buffers (e2.handles 6).1).val
    first n1 copy allocator e1 id data1 state1 = ok (.Ok (saved,post1,final1)) ∧
    second n2 allocator e2 id data2 slot state2 = ok (.Ok (post2,final2)) ∧
    TwoTransactionLaw next ordinary (image old) (image (bytesOf saved.val)) status (loader old) ∧
    next false true ∧ ordinary false () ∧
    loader old true () = some (bytesOf (e2.buffers (e2.handles 6).1).val) ∧
    status false = false ∧ status false ≠ true :=
  ⟨accepted1,accepted2,law _ _,⟨rfl,rfl⟩,True.intro,rfl,rfl,Bool.false_ne_true⟩

#print axioms law
#print axioms accepted_pair
end AspisR1.CPS_ParentBoundary
end
