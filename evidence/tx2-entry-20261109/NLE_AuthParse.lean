import NLE_AuthState
set_option autoImplicit false
noncomputable section
namespace NLE_Auth
open Aeneas Aeneas.Std Result VTop_Stages
/-- Occurrence 0, before any marker/common call. The SAME proof is parsed. -/
theorem parse_result {H : Type} (ops : Ops) (s : State H) :
 (parse ops s).result = (ops.op3 s.frame.proof >>= fun reply =>
  match reply with
  | .Ok variant => ok (.Ok {s with parsed := some variant})
  | .Err err => ok (.Err err)) := by
 unfold parse
 rw [NJU_Log.erase_bind]
 cases h : ops.op3 s.frame.proof with
 | fail err => rfl
 | div => rfl
 | ok reply => cases reply <;> rfl
/-- The input frame is preserved by the successful source step. -/
theorem parse_frame {H : Type} (s : State H) (variant : transport.Variant) :
 ({s with parsed := some variant} : State H).frame = s.frame := rfl
/-- Every nominal error variant terminates before either later occurrence. -/
theorem parse_reject {H : Type} (ops : Ops) (s : State H) (err : verifier.Error)
 (reply : ops.op3 s.frame.proof = ok (.Err err)) :
 G ops (fun _ => .div) s =
 ⟨ok (.Err err),[.parse s.frame.proof (ok (.Err err))]⟩ := by
 simp only [G,parse,NJU_Log.record,reply,NJU_Log.bind,tryR]
 rfl
#print parse_result
#print parse_reject
#print axioms parse_result
#print axioms parse_frame
#print axioms parse_reject
end NLE_Auth
