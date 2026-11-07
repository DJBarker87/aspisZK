import NND_AccountCarrier
set_option autoImplicit false
noncomputable section
namespace NND_ResultTotal
open Aeneas Aeneas.Std Result
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
 Total (NND_Carrier.outer f r) := by
 obtain ⟨a,ha⟩ := hr
 exact ⟨f a,by rw [ha]; rfl⟩

#print axioms equation
#print axioms pure
#print axioms bind
#print axioms outer
end NND_ResultTotal
end
