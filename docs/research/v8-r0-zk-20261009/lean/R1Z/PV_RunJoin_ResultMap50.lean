import R1Z.PV_RunJoin_WeightMap46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ResultMap50
open Aeneas Aeneas.Std Result
open PV_RunJoin_WeightMap46 (mapResult)

theorem bind {A B C : Type} (f : B → C) (m : Result A) (k : A → Result B) :
    mapResult f (m >>= k)=(do let a ← m;mapResult f (k a)) := by
  cases m <;> rfl
#print axioms bind
end R1Z.PV_RunJoin_ResultMap50
