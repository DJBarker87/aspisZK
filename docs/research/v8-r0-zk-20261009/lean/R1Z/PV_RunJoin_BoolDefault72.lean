import Aeneas
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BoolDefault72
open Aeneas Aeneas.Std Result

theorem complete (comparison : Result Bool)
    (success : (do let equal ← comparison;ok (decide (¬equal=true)))=ok false) :
    comparison=ok true := by
  cases h : comparison with
  | fail e => simp only [h] at success;cases success
  | div => simp only [h] at success;cases success
  | ok equal =>
    rw [h] at success
    cases equal with
    | false => cases success
    | true => rfl

#print axioms complete
end R1Z.PV_RunJoin_BoolDefault72
