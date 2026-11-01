import NEJ_ConcreteFrame
set_option autoImplicit false
noncomputable section
namespace NEJ_CommonSourceFrame
open Aeneas Aeneas.Std Result NED_PaymentCohorts NED_CommonEncodeCohort

/-- Complete emitted/model value plus byte frame, on the SAME arbitrary prestate.
Native source-window certificates are separate evidence; this statement does
not quantify over or rename a model as the frozen native implementation. -/
theorem result_and_frame (out : Array U8 216#usize) (magic : Array U8 4#usize)
    (kind : TK) (c : C) :
    ∃ result : Array U8 216#usize,
      AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.encode_common
        out magic (toRawKind kind) (toRawCommon c) = ok result ∧
      result = NBP_CommonBytes.encoded out magic kind c ∧
      ∀ k : Nat, k = 7 ∨ 148 ≤ k → result.val[k]? = out.val[k]? := by
  refine ⟨NBP_CommonBytes.encoded out magic kind c, result out magic kind c, rfl, ?_⟩
  intro k hk
  exact NEJ_ConcreteFrame.encoded_frame out magic kind c k hk

#print axioms result_and_frame
end NEJ_CommonSourceFrame
