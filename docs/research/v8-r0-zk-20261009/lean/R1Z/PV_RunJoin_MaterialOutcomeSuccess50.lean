import R1Z.PV_RunJoin_MaterialRun49
set_option autoImplicit false
namespace R1Z.PV_RunJoin_MaterialOutcomeSuccess50
open Aeneas Aeneas.Std Result ProverRwFull

theorem complete (request : Result PV_B2_F_AllocationTransport.Outcome)
    (r : Result (Array PV_RunJoin_MaterialVec49.S 1024#usize))
    (out : alloc.vec.Vec aspis_core.field.wide_exact.WideExact)
    (h : PV_RunJoin_MaterialRun49.outcome request r=ok (.Ok out)) :
    request=ok .supplied ∧ ∃ a,r=ok a ∧ PV_RunJoin_MaterialVec49.vec a=out := by
  cases request with
  | fail e => cases h
  | div => cases h
  | ok event =>
    cases event with
    | denied => cases h
    | supplied =>
      cases r with
      | fail e => cases h
      | div => cases h
      | ok a => exact ⟨rfl,a,rfl,core.result.Result.Ok.inj (Result.ok.inj h)⟩
#print axioms complete
end R1Z.PV_RunJoin_MaterialOutcomeSuccess50
