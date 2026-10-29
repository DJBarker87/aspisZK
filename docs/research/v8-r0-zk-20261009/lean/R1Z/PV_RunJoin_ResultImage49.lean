import R1Z.PV_RunJoin_WeightMap46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ResultImage49
open Aeneas Aeneas.Std Result
open PV_RunJoin_WeightMap46 (mapResult)
theorem success {A B : Type} (f : A → B) (r : Result A) (b : B)
    (h : mapResult f r=ok b) : ∃ a,r=ok a ∧ f a=b := by
  cases r with
  | fail e => cases h
  | div => cases h
  | ok a => exact ⟨a,rfl,Result.ok.inj h⟩

theorem injective {A B : Type} (f : A → B) (hf : Function.Injective f) :
    Function.Injective (mapResult f) := by
  intro a b h
  cases a <;> cases b <;> cases h
  first | rfl | exact congrArg Result.ok (hf rfl)
#print axioms success
#print axioms injective
end R1Z.PV_RunJoin_ResultImage49
