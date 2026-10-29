import R1Z.PV_RunJoin_ResultPost41
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ResultWitness51
open Aeneas Aeneas.Std Result PV_RunJoin_ResultPost41

theorem complete {A : Type} (m : Result A) : Post (fun a => m=ok a) m := by
  cases m <;> trivial
#print axioms complete
end R1Z.PV_RunJoin_ResultWitness51
