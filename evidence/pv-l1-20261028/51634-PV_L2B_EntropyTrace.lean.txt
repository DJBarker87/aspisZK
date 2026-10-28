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
theorem first_skips_second : checks 0=1 := rfl
#print axioms first_skips_second
theorem second_checks_both : checks 1=2 := rfl
#print axioms second_checks_both
theorem success_checks_both : checks 2=2 := rfl
#print axioms success_checks_both
theorem full_comparison_count_relabel {A B C D : Type} (f : A → C) (g : B → D)
    (n : Nat) (xs : List (Option A × Option B)) :
    ((branches n (xs.map (fun p => (p.1.map f,p.2.map g)))).map checks).sum =
      ((branches n xs).map checks).sum := by rw [branches_relabel]
#print axioms full_comparison_count_relabel
theorem first_reject_conditional (z : ℚ) (hz : z ≠ 0) (ht : 2-z ≠ 0) : z/(z+(1-z)*z) = 1/(2-z) := by
  rw [show z+(1-z)*z=z*(2-z) by ring]
  field_simp <;> ring
theorem entropy_q_valid (z : ℚ) (hz : 0<z) (hz1 : z≤1) :
    0<z+(1-z)*z ∧ z+(1-z)*z≤1 := by
  have hm : 0≤(1-z)*z := mul_nonneg (sub_nonneg.mpr hz1) hz.le
  constructor
  · linarith
  · nlinarith [sq_nonneg (1-z)]
#print axioms first_reject_conditional
#print axioms entropy_q_valid
theorem second_reject_conditional (z : ℚ) (hz : z ≠ 0) (ht : 2-z ≠ 0) : ((1-z)*z)/(z+(1-z)*z) = (1-z)/(2-z) := by
  rw [show z+(1-z)*z=z*(2-z) by ring]
  field_simp <;> ring
#print axioms second_reject_conditional
theorem conditional_class_total (z : ℚ) (ht : 2-z ≠ 0) : 1/(2-z)+(1-z)/(2-z)=1 := by field_simp; ring
#print axioms conditional_class_total
end PV_L2B_EntropyTrace
