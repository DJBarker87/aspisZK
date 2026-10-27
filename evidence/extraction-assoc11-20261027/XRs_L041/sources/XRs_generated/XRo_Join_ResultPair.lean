import XRo_Join_ResultTransport
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport
set_option autoImplicit false
namespace XRo_Join_ResultPair
/-- The emitted do-binder uses a let-pattern rather than a match. -/
theorem map_let_pair {A B F G : Type} (f : F → G) (p : A × B) (k : A → B → Result F) :
 mapR f (let (a,b) := p; k a b)=(let (a,b) := p; mapR f (k a b)) := by cases p; rfl
#print axioms map_let_pair
end XRo_Join_ResultPair
