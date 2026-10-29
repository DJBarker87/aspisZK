import Aeneas
namespace R1Z.PV_RDCD4_Option194
set_option autoImplicit false

def mapSource {A B : Type} (o : Option A) (f : A → B) : Option B :=
  match o with
  | some x => some (f x)
  | none => none

def andThenSource {A B : Type} (o : Option A) (f : A → Option B) : Option B :=
  match o with
  | some x => f x
  | none => none

theorem map_binding {A B : Type} (o : Option A) (f : A → B) :
    mapSource o f=o.map f := by cases o <;> rfl

theorem and_then_binding {A B : Type} (o : Option A) (f : A → Option B) :
    andThenSource o f=o.bind f := by cases o <;> rfl

/-- The concrete residual has no inhabited Some branch. -/
def residual {A : Type} (r : Option Empty) : Option A :=
  match r with
  | none => none
  | some e => nomatch e

theorem residual_none {A : Type} : residual (A:=A) none=none := rfl

/-- Dropping the unused concrete closure cannot mutate its captured reference.
Source closure captures are references/Copy values, with no user destructor. -/
theorem none_does_not_call {A B : Type} (f : A → Option B) :
    andThenSource none f=none := rfl

#print axioms map_binding
#print axioms and_then_binding
#print axioms residual_none
#print axioms none_does_not_call
end R1Z.PV_RDCD4_Option194
