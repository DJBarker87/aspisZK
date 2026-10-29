import R1Z.PV_RunJoin_ResultMap50
set_option autoImplicit false
namespace R1Z.PV_RunJoin_MappedSuccess50
open Aeneas Aeneas.Std Result
open PV_RunJoin_WeightMap46 (mapResult)

theorem complete {A B : Type} (f : A → B) (r : Result A) (out : B)
    (h : mapResult f r=ok out) : ∃ a,r=ok a ∧ f a=out := by
  cases r with
  | fail e => cases h
  | div => cases h
  | ok a => exact ⟨a,rfl,Result.ok.inj h⟩
#print axioms complete
end R1Z.PV_RunJoin_MappedSuccess50
