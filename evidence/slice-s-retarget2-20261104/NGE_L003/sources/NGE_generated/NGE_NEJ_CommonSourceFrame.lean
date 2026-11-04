import Lean
import NGE_NEJ_ConcreteFrame

set_option autoImplicit false
noncomputable section
namespace NGE_NEJ_CommonSourceFrame
open Aeneas Aeneas.Std Result NFY_NED_PaymentCohorts NFY_NED_CommonEncodeCohort

/-- Complete emitted/model value plus byte frame, on the SAME arbitrary prestate.
Native source-window certificates are separate evidence; this statement does
not quantify over or rename a model as the frozen native implementation. -/
theorem result_and_frame (out : Array U8 216#usize) (magic : Array U8 4#usize)
    (kind : TK) (c : C) :
    ∃ result : Array U8 216#usize,
      AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.encode_common
        out magic (toRawKind kind) (toRawCommon c) = ok result ∧
      result = NFY_NBP_CommonBytes.encoded out magic kind c ∧
      ∀ k : Nat, k = 7 ∨ 148 ≤ k → result.val[k]? = out.val[k]? := by
  refine ⟨NFY_NBP_CommonBytes.encoded out magic kind c, result out magic kind c, rfl, ?_⟩
  intro k hk
  exact NGE_NEJ_ConcreteFrame.encoded_frame out magic kind c k hk

#print axioms result_and_frame
end NGE_NEJ_CommonSourceFrame

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
