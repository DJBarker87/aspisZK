import KMX_CopyMeaning
set_option autoImplicit false
namespace NJC_CopyFrame

/-- Lift one bounded native copy window to its exact offset in the caller.
Pointer validity, nonoverlap, lengths and ownership remain caller obligations;
this theorem is the supplied KMX value law, not a replacement copy stub. -/
theorem window {A : Type} (source target : Nat → A) (offset width index : Nat) :
 KMX_CopyMeaning.loop (fun j=>source (offset+j)) target 0 width index=
 if index<width then source (offset+index) else target index :=
 KMX_CopyMeaning.copy_prefix _ _ width index

/-- Every untouched destination byte retains its arbitrary pre-state value. -/
theorem frame {A : Type} (source target : Nat → A) (start width index : Nat)
 (outside : index<start ∨ start+width≤index) :
 KMX_CopyMeaning.loop source target start width index=target index :=
 KMX_CopyMeaning.copy_frame source target start width index outside

/-- Disjoint caller windows compose without normalizing a whole buffer. -/
theorem compose {A : Type} (first second target : Nat → A)
 (a n b m index : Nat) (separate : a+n≤b ∨ b+m≤a)
 (inside : a≤index ∧ index<a+n) :
 KMX_CopyMeaning.loop second (KMX_CopyMeaning.loop first target a n) b m index=first index := by
 rw [frame second _ b m index (by omega),KMX_CopyMeaning.loop_spec,if_pos inside]

#print axioms window
#print axioms frame
#print axioms compose
end NJC_CopyFrame
