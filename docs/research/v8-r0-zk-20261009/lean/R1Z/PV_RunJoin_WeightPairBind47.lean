import R1Z.PV_RunJoin_WeightResult46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightPairBind47
open Aeneas Aeneas.Std Result

theorem complete {A B C D : Type} (p : A × B) (f : A → B → Result C)
    (k : C → Result D) :
    ((let (a,b) := p; f a b) >>= k)=(let (a,b) := p; f a b >>= k) := by
  cases p;rfl
#print axioms complete
end R1Z.PV_RunJoin_WeightPairBind47
