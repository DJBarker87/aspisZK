import NNH_Run5bCurrentShape
import LIB_VBegin
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_SemanticBegin
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

theorem returned (a : LIB_VCarriers.Prefix × LIB_VCarriers.Transcript) (env : RSL.Env)
 (c : LIB_VCarriers.Challenges) (t : LIB_VCarriers.Transcript)
 (called : LIB_VLib.beginValue a env = .ok (c,t)) :
 r1_wire.begin (LIB_VCode.digest env) (LIB_VCarriers.prefixRaw a.1) a.2 =
 .ok (.Ok (LIB_VCarriers.challengesRaw c),t) := by
 change LIB_VResult.value id (.error .Terminal) (LIB_VBegin.model a env) = .ok (c,t) at called
 have model : LIB_VBegin.model a env = .ok (.ok (c,t)) := by
  cases h : LIB_VBegin.model a env with
  | fail e => rw [h] at called; cases called
  | div => rw [h] at called; cases called
  | ok out => rw [h] at called; exact congrArg Result.ok called
 have exact_ := LIB_VBegin.model_exact a env
 rw [model,bind_tc_ok] at exact_
 cases raw : r1_wire.begin (LIB_VCode.digest env) (LIB_VCarriers.prefixRaw a.1) a.2 with
 | fail e => rw [raw] at exact_; cases exact_
 | div => rw [raw] at exact_; cases exact_
 | ok out =>
  rcases out with ⟨reply,after⟩
  cases reply with
  | Err e => rw [raw] at exact_; cases exact_
  | Ok cs =>
   rw [raw,bind_tc_ok] at exact_
   have same : (LIB_VCarriers.challengesRaw c,t)=(cs,after) :=
    Except.ok.inj (Result.ok.inj exact_)
   cases same
   rfl
#print axioms returned
end AspisR1.NNV_SemanticBegin
end
