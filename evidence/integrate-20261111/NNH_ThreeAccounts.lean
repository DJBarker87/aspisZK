import NNH_Libraries
set_option autoImplicit false
namespace NNH_ThreeAccounts

theorem shape {A : Type} (xs : List A) (length : xs.length=3) :
 ∃ a b c,xs=[a,b,c] := by
 cases xs with
 | nil => cases length
 | cons a xs => cases xs with
   | nil => cases length
   | cons b xs => cases xs with
     | nil => cases length
     | cons c xs => cases xs with
       | nil => exact ⟨a,b,c,rfl⟩
       | cons d xs => simp only [List.length_cons] at length; omega
#print axioms shape
end NNH_ThreeAccounts
