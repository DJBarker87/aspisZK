import R1Z.PV_RunJoin_SemanticMaterial50
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BoxSuccess50
open Aeneas Aeneas.Std Result ProverRwFull

theorem complete {A E : Type} (request : Result Unit) (a out : A)
    (h : (do let _ ← request;ok (core.result.Result.Ok a : core.result.Result A E))=ok (.Ok out)) :
    request=ok () ∧ out=a := by
  cases request with
  | fail e => cases h
  | div => cases h
  | ok u =>
    cases u
    exact ⟨rfl,(core.result.Result.Ok.inj (Result.ok.inj h)).symm⟩
#print axioms complete
end R1Z.PV_RunJoin_BoxSuccess50
