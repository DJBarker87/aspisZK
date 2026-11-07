import NLT_Reseed
set_option autoImplicit false
noncomputable section
namespace NLT_ReseedTransport
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved NKE_Free
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep NLT_NativeInvocation
/-- The SAME records and actual decoded replies survive re-seeding; nothing
is re-run, renamed, re-observed or equated to an independently supplied log. -/
theorem forward {H : Bytes → State} {X : Type} {d : aspis_core.digest.Digest32 X} {hash : X}
 {A : Type} (left right : Program Event A) (same : NLT_Reseed.Same left right)
 (result : Result A) (records : List (Occurrence H d hash))
 (invocation : Invocation H d hash left result records) :
 Invocation H d hash right result records := by
 induction same generalizing result records with
 | ret value => cases invocation;exact .ret value
 | prim reply left right tail ih =>
   cases invocation with
   | prim_ok value _ _ _ after => exact .prim_ok value right result records (ih value _ _ after)
   | prim_fail error _ => exact .prim_fail error right
   | prim_div _ => exact .prim_div right
 | call codec old fresh left right questions tail ih =>
   cases invocation with
   | call_ok _ _ _ record entered value decoded _ rest after =>
     exact .call_ok codec fresh right record (entered.trans questions) value decoded result rest (ih value _ _ after)
   | call_fail _ _ _ record entered error decoded =>
     exact .call_fail codec fresh right record (entered.trans questions) error decoded
   | call_div _ _ _ record entered decoded =>
     exact .call_div codec fresh right record (entered.trans questions) decoded
set_option pp.proofs false
#print forward
#print axioms forward
end NLT_ReseedTransport
