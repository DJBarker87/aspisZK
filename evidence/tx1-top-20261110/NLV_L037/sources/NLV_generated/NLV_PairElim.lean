import NLV_Emitted
set_option autoImplicit false
namespace AspisR1.NLV_PairElim
theorem elim {A B C : Type} (p : A × B) (f : A → B → C) :
 (match p with | (a,b) => f a b) = f p.1 p.2 := by cases p; rfl
#print axioms elim
end AspisR1.NLV_PairElim
