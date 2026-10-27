import Aeneas
namespace R1Z.PV_CBL_ArrayImage
set_option autoImplicit false

def image {T : Type} (src : List T) (zero : T) (n k : Nat) : List T :=
  src.take k ++ List.replicate (n-k) zero

theorem start {T : Type} (src : List T) (zero : T) (n : Nat) :
    image src zero n 0 = List.replicate n zero := by simp [image]

theorem length {T : Type} (src : List T) (zero : T) (n k : Nat)
    (hs : k≤src.length) (hn : k≤n) : (image src zero n k).length=n := by
  simp only [image,List.length_append,List.length_take,List.length_replicate,Nat.min_eq_left hs]
  omega

theorem finish {T : Type} (src : List T) (zero : T) :
    image src zero src.length src.length = src := by simp [image]

/-- One copied cell extends the copied without evaluating any concrete array. -/
theorem write_head {T : Type} (copied suffix : List T) (zero value : T) :
    (copied ++ zero::suffix).set copied.length value = copied ++ value::suffix := by
  induction copied with
  | nil => rfl
  | cons head tail ih =>
    change head :: ((tail ++ zero::suffix).set tail.length value) =
      head :: (tail ++ value::suffix)
    rw [ih]

#print axioms start
#print axioms length
#print axioms finish
#print axioms write_head
end R1Z.PV_CBL_ArrayImage
