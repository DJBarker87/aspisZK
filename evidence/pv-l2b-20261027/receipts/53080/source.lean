import PV_L2B_SamplerLaw
import PV_L2B_Rejection
set_option autoImplicit false
namespace PV_L2B_EntropyTrace
-- Per successful 64-byte fill: 0=first zero (second check skipped),
-- 1=second zero, 2=both nonzero. OS error schedule is a separate input.
def kind {A B : Type} : Option A × Option B → Nat
 | (none, _) => 0
 | (some _, none) => 1
 | (some _, some _) => 2
def checks (kind : Nat) : Nat := if kind=0 then 1 else 2
def branches {A B : Type} : Nat → List (Option A × Option B) → List Nat
 | 0, _ => []
 | _+1, [] => []
 | n+1, x::xs => if kind x=2 then [2] else kind x :: branches n xs
theorem first_zero {A B : Type} (b : Option B) : kind ((none : Option A), b)=0 := rfl
#print axioms first_zero
theorem second_zero {A B : Type} (a : A) : kind (some a, (none : Option B))=1 := rfl
#print axioms second_zero
theorem accepted_pair {A B : Type} (a : A) (b : B) : kind (some a,some b)=2 := rfl
#print axioms accepted_pair
theorem kind_relabel {A B C D : Type} (f : A → C) (g : B → D) (p : Option A × Option B) :
    kind (p.1.map f,p.2.map g)=kind p := by
  rcases p with ⟨a,b⟩; cases a <;> cases b <;> rfl
#print axioms kind_relabel
theorem branches_relabel {A B C D : Type} (f : A → C) (g : B → D)
    (n : Nat) (xs : List (Option A × Option B)) :
    branches n (xs.map (fun p => (p.1.map f,p.2.map g)))=branches n xs := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    cases xs with
    | nil => rfl
    | cons x xs => simp only [List.map_cons,branches,kind_relabel,ih]
#print axioms branches_relabel
end PV_L2B_EntropyTrace
