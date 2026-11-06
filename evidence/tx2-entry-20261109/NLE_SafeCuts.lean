import NLE_NativeTags
set_option autoImplicit false
namespace NLE_SafeCuts
open Aeneas Aeneas.Std VTop_Stages
/-- ONLY pointer/length metadata, not byte identity or typed provenance. -/
structure Descriptor where
 base : Nat
 length : Nat
structure State where
 publicBytes : Descriptor
 proof : Descriptor
 checkpoint : Descriptor
structure Log where
 calls : Nat
 publicBytes : Descriptor
 proof : Descriptor
 checkpoint : Descriptor
/-- Reviewed assertion schema of the safe parse segment in NLE_auth_steps.patch.
Complete tag coverage is proved in NLE_NativeTags. No payload frame is invented. -/
def ParseCut (before : State) (reply : core.result.Result transport.Variant verifier.Error)
 (after : core.result.Result State verifier.Error) (log : Log) : Prop :=
 (match reply with | .Ok _ => after = .Ok before | .Err err => after = .Err err) ∧
 log.calls = 1 ∧ log.proof = before.proof
/-- Safe common-tail assertion schema; this states no whole child-world frame. -/
def CommonCut (before : State) (reply after : core.result.Result Unit verifier.Error) (log : Log) : Prop :=
 after = reply ∧ log.calls = 1 ∧ log.publicBytes = before.publicBytes ∧
 log.proof = before.proof ∧ log.checkpoint = before.checkpoint
def Scope (state : State) : Prop :=
 state.publicBytes.length = 1880 ∧ state.proof.length = 57607 ∧ state.checkpoint.length = 1768
/-- The successful parse continuation keeps every metadata clause; a returned
error does not produce an independently chosen normal successor. -/
theorem parse_continuation (before post : State)
 (reply : core.result.Result transport.Variant verifier.Error) (log : Log)
 (native : ParseCut before reply (.Ok post) log) (scope : Scope before) :
 post = before ∧ Scope post := by
 cases reply with
 | Err err => cases native.1
 | Ok variant => cases native.1; exact ⟨rfl,scope⟩
theorem parse_error (before : State) (err : verifier.Error)
 (after : core.result.Result State verifier.Error) (log : Log)
 (native : ParseCut before (.Err err) after log) : after = .Err err := native.1
theorem common_reply (before : State) (reply after : core.result.Result Unit verifier.Error)
 (log : Log) (native : CommonCut before reply after log) : after = reply := native.1
#print ParseCut
#print CommonCut
#print parse_continuation
#print axioms parse_continuation
#print axioms parse_error
#print axioms common_reply
end NLE_SafeCuts
