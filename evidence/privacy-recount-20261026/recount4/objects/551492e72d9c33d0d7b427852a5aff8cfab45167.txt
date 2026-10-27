import Aeneas
/-! PREPARED: symbolic array carrier transport; no concrete array reduction. -/
set_option autoImplicit false
namespace R1Z.PV_CB_ArrayTransport
open Aeneas Aeneas.Std

def mapArray {A B : Type} {n : Usize} (f : A → B) (x : Array A n) : Array B n :=
  ⟨x.val.map f, by simpa only [List.length_map] using x.property⟩

theorem roundtrip {A B : Type} {n : Usize} (f : A → B) (g : B → A)
    (h : ∀ x, g (f x) = x) (x : Array A n) :
    mapArray g (mapArray f x) = x := by
  apply Subtype.ext
  simp only [mapArray, List.map_map]
  change x.val.map (fun a => g (f a)) = x.val
  simp only [h]
  exact List.map_id x.val

#print axioms roundtrip
end R1Z.PV_CB_ArrayTransport
