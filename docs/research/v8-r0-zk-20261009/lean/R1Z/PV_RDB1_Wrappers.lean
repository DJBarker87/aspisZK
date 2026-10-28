import Aeneas
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDB1_Wrappers

/-- The deployed ManuallyDrop uses a MaybeDangling transparent field. On a
live value its shared/mutable projections reach exactly the same T. -/
structure MaybeDangling (T : Type) where
  value : T
structure ManuallyDrop (T : Type) where
  value : MaybeDangling T

def new {T : Type} (x : T) : ManuallyDrop T := ⟨⟨x⟩⟩
def deref {T : Type} (x : ManuallyDrop T) : T := x.value.value

def derefMut {T : Type} (x : ManuallyDrop T) : T × (T → ManuallyDrop T) :=
  (x.value.value,fun updated => ⟨⟨updated⟩⟩)

theorem deref_complete {T W R : Type} (x : T) (w : W) (use : T → W → Result R) :
    use (deref (new x)) w = use x w := rfl

/-- The updated mutable value is restored through BOTH wrapper fields. The
backward continuation is never discarded. -/
theorem deref_mut_complete {T : Type} (x updated : T) :
    (derefMut (new x)).1=x ∧ (derefMut (new x)).2 updated=new updated := ⟨rfl,rfl⟩

/-- Consuming a wrapper calls a shared drop primitive once on the live value;
wrapping neither allocates nor duplicates the destructor obligation. -/
theorem consume_complete {T W R : Type} (x : T) (w : W)
    (consume : T → W → Result R) : consume (deref (new x)) w=consume x w := rfl

#print axioms deref_complete
#print axioms deref_mut_complete
#print axioms consume_complete
end R1Z.PV_RDB1_Wrappers
