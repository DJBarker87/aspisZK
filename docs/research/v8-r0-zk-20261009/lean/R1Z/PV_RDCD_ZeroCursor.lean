import R1Z.PV_RDCD_ZeroWorld
set_option autoImplicit false
namespace R1Z.PV_RDCD_ZeroCursor
open PV_RDCD_ZeroWorld

/-- Address projection of the deployed non-ZST IterMut::next. The source
increments the cursor before returning the old exclusive reference. The
valid-array domain supplies provenance and one-past validity separately. -/
def next (address finish : Nat) : Option (Nat × Nat) :=
  if address=finish then none else some (address,address+1)

theorem next_live (address n : Nat) :
    next address (address+(n+1))=some (address,address+1) := by
  have h : address≠address+(n+1) := by omega
  simp only [next,h,ite_false]

theorem next_empty (address : Nat) : next address address=none := by
  simp only [next,ite_true]

/-- The fuel is the valid u8 slice length, not an extra execution bound. -/
def run {F : Type} (finish : Nat) : Nat → Nat → World F → World F
  | 0,_,w => w
  | n+1,address,w =>
    match next address finish with
    | none => w
    | some (old,new) => run finish n new (byte old w)

theorem source {F : Type} (address n : Nat) (w : World F) :
    run (address+n) n address w=native address n w := by
  induction n generalizing address w with
  | zero => rfl
  | succ n ih =>
    simp only [run,next_live,native]
    have h : address+(n+1)=(address+1)+n := by omega
    rw [h]
    exact ih (address+1) (byte address w)

/-- Adding the semicolon to the1.9 Drop delegate changes no Unit result. -/
theorem drop_semicolon {A : Type} (f : A → Unit) (x : A) :
    (let _ := f x; ())=f x := by cases f x; rfl

/-- Casting a valid byte-array pointer to its first byte preserves its
address; casting the byte pointer to () for asm preserves that address too.
This theorem records the address projection, not a provenance model. -/
def addressCast (address : Nat) := address

theorem casts (address : Nat) : addressCast (addressCast address)=address := rfl

#print axioms next_live
#print axioms next_empty
#print axioms source
#print axioms drop_semicolon
#print axioms casts
end R1Z.PV_RDCD_ZeroCursor
