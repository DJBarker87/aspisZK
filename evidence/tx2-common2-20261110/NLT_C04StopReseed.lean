import NLT_C04Stop
import NLT_ReseedTransport
set_option autoImplicit false
noncomputable section
namespace NLT_C04StopReseed
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved NKE_Free
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep NLT_NativeInvocation
/-- Re-seed only the source reference; the ACTUAL stopped native cut remains
identical and no reference reply is required at that cut. -/
theorem forward {H : Bytes → State} {X : Type} {d : aspis_core.digest.Digest32 X} {hash : X}
 {A : Type} (left right : Program Event A) (same : NLT_Reseed.Same left right)
 (records : List (Occurrence H d hash)) (cut : NLT_C04Stop.Cut H)
 (stopped : NLT_C04Stop.At H d hash left records cut) : NLT_C04Stop.At H d hash right records cut := by
 induction same generalizing records with
 | ret value => cases stopped
 | prim reply left right tail ih =>
   cases stopped with
   | prim_ok value _ _ _ after => exact .prim_ok value right records cut (ih value _ after)
 | call codec old fresh left right questions tail ih =>
   cases stopped with
   | call_ok _ _ _ record entered value decoded rest _ after =>
     exact .call_ok codec fresh right record (entered.trans questions) value decoded rest cut (ih value _ after)
   | stopped _ _ _ _ entered =>
     exact .stopped codec fresh right cut (questions.symm.trans entered)
set_option pp.proofs false
#print forward
#print axioms forward
end NLT_C04StopReseed
