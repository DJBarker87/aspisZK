import ExtractorListWorkM10

set_option autoImplicit false
namespace AspisR1.AllocationListConsumersM10

def filterMapCells {A : Type} (heap : A → Nat) : List A → Nat
  | [] => 1
  | x::xs => heap x+filterMapCells heap xs+2

theorem filterMap_paid {A B : Type} (f : A → Option B × Nat) (heap : A → Nat)
    (h : ∀ x, heap x ≤ (f x).2) (xs : List A) :
    filterMapCells heap xs ≤ (ExtractorListWorkM10.filterMap f xs).2 := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih => exact Nat.add_le_add_right (Nat.add_le_add (h x) ih) 2

def findMapCells {A B : Type} (f : A → Option B × Nat) (heap : A → Nat) : List A → Nat
  | [] => 1
  | x::xs =>
    match (f x).1 with
    | some _ => heap x+1
    | none => heap x+findMapCells f heap xs+1

theorem findMap_paid {A B : Type} (f : A → Option B × Nat) (heap : A → Nat)
    (h : ∀ x, heap x ≤ (f x).2) (xs : List A) :
    findMapCells f heap xs ≤ (ExtractorListWorkM10.findMap f xs).2 := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    have hx := h x
    cases ho : (f x).1 <;> simp only [findMapCells,ExtractorListWorkM10.findMap,ho] <;> omega

#print axioms filterMap_paid
#print axioms findMap_paid
end AspisR1.AllocationListConsumersM10
