import R1Z.PV_RunJoin_NativeResult55
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NativeProjection55
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultRelation55

def observe {A C T : Type} (decode : A → C) :
    Result (core.result.Result (A × prover.MaskedFixtureAudit) verifier.Error × T) → Option C
  | .ok (.Ok (a,_),_) => some (decode a)
  | _ => none

theorem complete {A B C T : Type} (decode : A → C) (encode : B → C)
    (a : Result (core.result.Result (A × prover.MaskedFixtureAudit) verifier.Error × T))
    (b : Result (core.result.Result (B × prover.MaskedFixtureAudit) verifier.Error × T))
    (h : Rel (PV_RunJoin_NativeResult55.Output (fun x y => decode x=encode y)) a b) :
    observe decode a=(observe id b).map encode := by
  cases h with
  | fail e => rfl
  | div => rfl
  | @ok aa bb hr =>
    rcases aa with ⟨ar,ast⟩
    rcases bb with ⟨br,bst⟩
    rcases hr with ⟨hc,hs⟩
    cases hc with
    | err e => rfl
    | @ok x y hv =>
      rcases x with ⟨av,auditA⟩
      rcases y with ⟨bv,auditB⟩
      exact congrArg some hv.1
#print axioms observe
#print axioms complete
end R1Z.PV_RunJoin_NativeProjection55
