import LIB_Carriers
set_option autoImplicit false
noncomputable section
namespace LIB_ResultTotal
open Aeneas Aeneas.Std Result
def mapOuter {A B : Type} (f : A → B) : Result A → Result B
 | .ok x => .ok (f x)
 | .fail e => .fail e
 | .div => .div
/-- Value totality of a selected pure decoder, not runtime syscall totality. -/
def Total {A : Type} (r : Result A) : Prop := ∃ a, r = ok a

def value {A : Type} (r : Result A) (h : Total r) : A := Classical.choose h

theorem equation {A : Type} (r : Result A) (h : Total r) : r = ok (value r h) :=
 Classical.choose_spec h

theorem pure {A : Type} (a : A) : Total (ok a) := ⟨a,rfl⟩

theorem bind {A B : Type} (r : Result A) (k : A → Result B) (hr : Total r)
 (hk : ∀ a, Total (k a)) : Total (r >>= k) := by
 obtain ⟨a,ha⟩ := hr
 rw [ha]
 exact hk a

theorem outer {A B : Type} (r : Result A) (f : A → B) (hr : Total r) :
 Total (mapOuter f r) := by
 obtain ⟨a,ha⟩ := hr
 exact ⟨f a,by rw [ha]; rfl⟩

#print axioms equation
#print axioms pure
#print axioms bind
#print axioms outer
end LIB_ResultTotal
end
