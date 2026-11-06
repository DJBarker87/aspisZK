import NJR_FlushComposition
set_option autoImplicit false
noncomputable section
namespace NKE_Stores
/-- Native one-window post-state, with the full unselected frame. -/
def put {A : Type} (values before : List A) (i : Nat) : List A :=
 match values[i]? with | none => before | some value => before.set i value

def G {A : Type} (values before : List A) : Nat → List A
 | 0 => before
 | n+1 => put values (G values before n) n

theorem length {A : Type} (values before : List A) (n : Nat) :
 (G values before n).length=before.length := by
 induction n with
 | zero => rfl
 | succ n ih => simp only [G,put];split <;> simp_all only [List.length_set]

theorem step {A : Type} (values before : List A) (size : values.length=before.length)
 (i : Nat) (inside : i<before.length) :
 ∀ j,j<before.length → (G values before (i+1))[j]?=
 if i=j then values[i]? else (G values before i)[j]? := by
 intro j _
 have hi : i<values.length := by omega
 obtain ⟨value,read⟩ := List.getElem?_eq_some_iff.mpr ⟨hi,rfl⟩
 simp only [G,put,read]
 by_cases same : i=j
 · subst j
   rw [if_pos rfl,List.getElem?_set_self (by rw [length];exact inside)]
 · rw [if_neg same,List.getElem?_set_ne same]

theorem complete {A : Type} (values before : List A) (size : values.length=before.length) :
 G values before before.length=values := by
 have invariant : ∀ n,n≤before.length → ∀ j,j<n →
  (G values before n)[j]?=values[j]? := by
  intro n
  induction n with
  | zero => intro _ j h;omega
  | succ n ih =>
   intro hn j hj
   rw [step values before size n (by omega) j (by omega)]
   by_cases same : n=j
   · subst j;rw [if_pos rfl]
   · rw [if_neg same];exact ih (by omega) j (by omega)
 apply List.ext_getElem?
 intro j
 by_cases inside : j<before.length
 · exact invariant before.length (by omega) j inside
 · rw [List.getElem?_eq_none (by rw [length];omega),List.getElem?_eq_none (by omega)]
#print axioms length
#print axioms step
#print axioms complete
end NKE_Stores
