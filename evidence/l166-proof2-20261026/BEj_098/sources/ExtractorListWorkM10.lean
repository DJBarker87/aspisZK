import ExtractorWorkMonad

set_option autoImplicit false
namespace AspisR1.ExtractorListWorkM10

def filterMap {A B : Type} (f : A → Option B × Nat) : List A → List B × Nat
  | [] => ([],1)
  | x::xs =>
    let a := f x
    let b := filterMap f xs
    ((match a.1 with | none => b.1 | some y => y::b.1),a.2+b.2+2)

theorem filterMap_value {A B : Type} (f : A → Option B × Nat) (xs : List A) :
    (filterMap f xs).1 = xs.filterMap (fun x => (f x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [filterMap, List.filterMap_cons]
    cases (f x).1 <;> simp only [ih]

theorem filterMap_work {A B : Type} (f : A → Option B × Nat) (xs : List A)
    (C : Nat) (h : ∀ x ∈ xs, (f x).2 ≤ C) :
    (filterMap f xs).2 ≤ xs.length*(C+2)+1 := by
  induction xs with
  | nil => simp [filterMap]
  | cons x xs ih =>
    have hh := h x List.mem_cons_self
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    change _+_+2 ≤ _
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem filterMap_length {A B : Type} (f : A → Option B × Nat) (xs : List A) :
    (filterMap f xs).1.length ≤ xs.length := by
  rw [filterMap_value]
  exact List.length_filterMap_le _ _

def filter {A : Type} (p : A → Bool × Nat) (xs : List A) : List A × Nat :=
  filterMap (fun x => ((if (p x).1 then some x else none),(p x).2)) xs

theorem filter_value {A : Type} (p : A → Bool × Nat) (xs : List A) :
    (filter p xs).1 = xs.filter (fun x => (p x).1) := by
  rw [filter, filterMap_value]
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hp : (p x).1 <;> simp [hp,ih]

theorem filter_work {A : Type} (p : A → Bool × Nat) (xs : List A)
    (C : Nat) (h : ∀ x ∈ xs, (p x).2 ≤ C) :
    (filter p xs).2 ≤ xs.length*(C+2)+1 := filterMap_work _ xs C h

def findMap {A B : Type} (f : A → Option B × Nat) : List A → Option B × Nat
  | [] => (none,1)
  | x::xs =>
    let a := f x
    match a.1 with
    | some y => (some y,a.2+1)
    | none => let b := findMap f xs; (b.1,a.2+b.2+1)

theorem findMap_value {A B : Type} (f : A → Option B × Nat) (xs : List A) :
    (findMap f xs).1 = xs.findSome? (fun x => (f x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [findMap, List.findSome?_cons]
    cases (f x).1 <;> simp only [ih]

theorem findMap_work {A B : Type} (f : A → Option B × Nat) (xs : List A)
    (C : Nat) (h : ∀ x ∈ xs, (f x).2 ≤ C) :
    (findMap f xs).2 ≤ xs.length*(C+1)+1 := by
  induction xs with
  | nil => simp [findMap]
  | cons x xs ih =>
    have hh := h x List.mem_cons_self
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [findMap]
    split <;> dsimp only <;> simp only [List.length_cons, Nat.add_mul, Nat.one_mul] <;> omega

#print axioms filterMap_value
#print axioms filterMap_work
#print axioms filterMap_length
#print axioms filter_value
#print axioms filter_work
#print axioms findMap_value
#print axioms findMap_work
end AspisR1.ExtractorListWorkM10
