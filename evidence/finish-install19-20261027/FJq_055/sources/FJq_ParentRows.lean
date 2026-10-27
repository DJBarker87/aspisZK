import FJq_ReferenceRecord
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_ParentRows
open Aeneas Aeneas.Std Result AspisR1ClaimsUnrolledParent
/-- Preserve all three decoder returns and their actual complete output array. -/
theorem reached (ext : External) (record : Record) (out : Claims)
    (run : decodeRows ext record=ok (.Ok out)) :
    ∃ a b c : Row,
      ext.decode 29#usize record 0#usize=ok (.Ok a) ∧
      ext.decode 29#usize record 29#usize=ok (.Ok b) ∧
      ext.decode 29#usize record 58#usize=ok (.Ok c) ∧
      out=(⟨[a,b,c],by simp⟩ : Claims) := by
  unfold decodeRows at run
  obtain ⟨sa,ha,run⟩:=FIv_Map.bind_success _ _ _ run
  cases sa with
  | Err e=>cases run
  | Ok a=>
    obtain ⟨sb,hb,run⟩:=FIv_Map.bind_success _ _ _ run
    cases sb with
    | Err e=>cases run
    | Ok b=>
      obtain ⟨sc,hc,run⟩:=FIv_Map.bind_success _ _ _ run
      cases sc with
      | Err e=>cases run
      | Ok c=>exact ⟨a,b,c,ha,hb,hc,(core.result.Result.Ok.inj (Result.ok.inj run)).symm⟩
#print axioms reached
end AspisR1.FJq_ParentRows
end
