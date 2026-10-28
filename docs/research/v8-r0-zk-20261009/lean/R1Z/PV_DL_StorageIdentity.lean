import R1Z.PV_DL_StorageBuild
open Aeneas Aeneas.Std Result
namespace R1Z.PV_DL_StorageIdentity
open PV_CBL_GenericArrayPower PV_CBL_LibraryShapes
set_option autoImplicit false

theorem zero_array {T : Type} (a b : Array T 0#usize) : a=b := by
  apply Subtype.ext
  have ha : a.val=[] := List.length_eq_zero_iff.mp a.property
  have hb : b.val=[] := List.length_eq_zero_iff.mp b.property
  rw [ha,hb]

theorem left_half {T : Type} (k : Nat) (a b : Storage T k) :
    (flatten k a++flatten k b).take (2^k)=flatten k a := by
  simpa only [length] using (List.take_left (l₁ := flatten k a) (l₂ := flatten k b))

theorem right_half {T : Type} (k : Nat) (a b : Storage T k) :
    (flatten k a++flatten k b).drop (2^k)=flatten k b := by
  simpa only [length] using (List.drop_left (l₁ := flatten k a) (l₂ := flatten k b))

theorem injective {T : Type} (k : Nat) (a b : Storage T k)
    (h : flatten k a=flatten k b) : a=b := by
  induction k with
  | zero =>
    have ha1 : a.parent1.val=[] := List.length_eq_zero_iff.mp a.parent1.property
    have ha2 : a.parent2.val=[] := List.length_eq_zero_iff.mp a.parent2.property
    have hb1 : b.parent1.val=[] := List.length_eq_zero_iff.mp b.parent1.property
    have hb2 : b.parent2.val=[] := List.length_eq_zero_iff.mp b.parent2.property
    simp only [flatten,PV_CBL_GenericArrayFlatten.odd,ha1,ha2,hb1,hb2,
      List.nil_append,List.singleton_inj] at h
    have h1 := zero_array a.parent1 b.parent1
    have h2 := zero_array a.parent2 b.parent2
    rcases a with ⟨a1,a2,av⟩
    rcases b with ⟨b1,b2,bv⟩
    cases h1;cases h2;cases h;rfl
  | succ k ih =>
    change flatten k a.parent1++flatten k a.parent2=
      flatten k b.parent1++flatten k b.parent2 at h
    have left : flatten k a.parent1=flatten k b.parent1 := by
      have ht := congrArg (List.take (2^k)) h
      simpa only [left_half] using ht
    have right : flatten k a.parent2=flatten k b.parent2 := by
      have ht := congrArg (List.drop (2^k)) h
      simpa only [right_half] using ht
    have h1 := ih a.parent1 b.parent1 left
    have h2 := ih a.parent2 b.parent2 right
    rcases a with ⟨a1,a2,am⟩
    rcases b with ⟨b1,b2,bm⟩
    cases am;cases bm;cases h1;cases h2;rfl

theorem rebuild {T : Type} [Inhabited T] (k : Nat) (a : Storage T k) :
    PV_DL_StorageBuild.build k (fun i => (flatten k a)[i]!)=a := by
  apply injective k
  exact PV_DL_StorageBuild.reconstruct k _ (length k a)

#print axioms zero_array
#print axioms left_half
#print axioms right_half
#print axioms injective
#print axioms rebuild
end R1Z.PV_DL_StorageIdentity
