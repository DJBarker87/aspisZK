import R1Z.PV_RunJoin_WeightMap46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightResult46
open Aeneas Aeneas.Std Result PV_RunJoin_WeightMap46

theorem shared_bind {A B C : Type} (f : B → C) (r : Result A) (k : A → Result B) :
    mapResult f (r >>= k)=(r >>= fun a => mapResult f (k a)) := by
  cases r <;> rfl

theorem identity {A : Type} (r : Result A) : mapResult (fun x => x) r=r := by
  cases r <;> rfl

#print axioms shared_bind
#print axioms identity
end R1Z.PV_RunJoin_WeightResult46
