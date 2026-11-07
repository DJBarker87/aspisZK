import NMP_EmittedContext
set_option autoImplicit false
namespace AspisR1.NMP_Install130
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted
/-- r1_semantic.rs75-80, deployed detail-phases OFF: let _=(obs,i).
The observer function is never inspected or invoked by this child. -/
def mark (_ : Observer) (_ : U8) : Result Unit := .ok ()
theorem silent (obs : Observer) (i : U8) : mark obs i = .ok () := rfl
#print axioms silent
end AspisR1.NMP_Install130
