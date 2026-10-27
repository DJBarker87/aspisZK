import Std
set_option autoImplicit false
namespace R1Z.PV_CB3_StagedPair
/-- Eliminate product binders before reasoning about a branch they enclose. -/
theorem eliminate {A B C : Type} (p : A × B) (f : A → B → C) :
    (let (a,b) := p; f a b) = f p.1 p.2 := by cases p; rfl
#print axioms eliminate
end R1Z.PV_CB3_StagedPair
