import NNH_064ResumeStops
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_064Prefix
open Aeneas Aeneas.Std VTop_Stages NLW_Full064
/-- Source computation, not selection from a Spec. None exposes exactly the
unimplemented continuation after an actual successful resume; it must never
be installed as a total I.f064 or treated as an abort. -/
def run (env : RSL.Env) (r : NP6_StdModel.Reservation) (pub proof ck : Slice U8) :
 Option (RSL.Obs (Except verifier.Error Unit)) :=
 match NLE_ParseInstall.parse proof with
 | .fail _ => some ⟨.abort,[]⟩
 | .div => some ⟨.diverge,[]⟩
 | .ok (.Err e) => some ⟨.ret (.error e),[]⟩
 | .ok (.Ok _) =>
  let events := NNC_DigestTrace.render (NNH_064ResumeRecord.trace env r pub proof ck)
  match NNH_064ResumeError.reply env r pub proof ck with
  | .fail _ => some ⟨.abort,events⟩
  | .div => some ⟨.diverge,events⟩
  | .ok (.Err e) => some ⟨.ret (.error e),events⟩
  | .ok (.Ok _) => none

/-- Every computed endpoint is the actual native prefix in the unchanged
weak law. No child success, Root0, chosen native witness or empty renderer. -/
theorem weak {Ambient : Type} (env : RSL.Env) (r : NP6_StdModel.Reservation)
 (pub proof ck : Slice U8) (world : NLM_PacketTypes.World Ambient)
 (o : RSL.Obs (Except verifier.Error Unit)) (endpoint : run env r pub proof ck=some o) :
 NNC_ObservedLaw.w (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env) () world
  (LIB_Carriers.bytes pub) (LIB_Carriers.bytes proof) (LIB_Carriers.bytes ck) env o := by
 cases parsed : NLE_ParseInstall.parse proof with
 | fail e =>
  have initial := NNH_064Parser.weak env pub proof ck world (fun v same => by rw [parsed] at same; cases same)
  simp only [run,parsed,Option.some.injEq] at endpoint
  subst o
  simpa only [LIBB_Tx2EnvTrace.observation,LIBB_Tx2EnvTrace.events,LIBB_Tx2EnvCode.code,parsed]
   using initial
 | div =>
  have initial := NNH_064Parser.weak env pub proof ck world (fun v same => by rw [parsed] at same; cases same)
  simp only [run,parsed,Option.some.injEq] at endpoint
  subst o
  simpa only [LIBB_Tx2EnvTrace.observation,LIBB_Tx2EnvTrace.events,LIBB_Tx2EnvCode.code,parsed]
   using initial
 | ok reply => cases reply with
   | Err e =>
    have initial := NNH_064Parser.weak env pub proof ck world (fun v same => by rw [parsed] at same; cases same)
    simp only [run,parsed,Option.some.injEq] at endpoint
    subst o
    simpa only [LIBB_Tx2EnvTrace.observation,LIBB_Tx2EnvTrace.events,LIBB_Tx2EnvCode.code,parsed]
     using initial
   | Ok v =>
    cases resumed : NNH_064ResumeError.reply env r pub proof ck with
    | fail e =>
     simp only [run,parsed,resumed,Option.some.injEq] at endpoint
     subst o
     exact NNH_064ResumeStops.fail env r pub proof ck world v parsed e resumed
    | div =>
     simp only [run,parsed,resumed,Option.some.injEq] at endpoint
     subst o
     exact NNH_064ResumeStops.diverge env r pub proof ck world v parsed resumed
    | ok reply => cases reply with
      | Err e =>
       simp only [run,parsed,resumed,Option.some.injEq] at endpoint
       subst o
       exact NNH_064ResumeNative.weak env r pub proof ck world v parsed e resumed
      | Ok pair =>
       simp only [run,parsed,resumed,reduceCtorEq] at endpoint

/-- The exact uncovered continuation, derived from the source computation. -/
theorem remaining (env : RSL.Env) (r : NP6_StdModel.Reservation) (pub proof ck : Slice U8)
 (unfinished : run env r pub proof ck=none) :
 ∃ v p a, NLE_ParseInstall.parse proof=.ok (.Ok v) ∧
 NNH_064ResumeError.reply env r pub proof ck=.ok (.Ok (p,a)) := by
 cases parsed : NLE_ParseInstall.parse proof with
 | fail e => simp only [run,parsed,reduceCtorEq] at unfinished
 | div => simp only [run,parsed,reduceCtorEq] at unfinished
 | ok reply => cases reply with
   | Err e => simp only [run,parsed,reduceCtorEq] at unfinished
   | Ok v =>
    cases resumed : NNH_064ResumeError.reply env r pub proof ck with
    | fail e => simp only [run,parsed,resumed,reduceCtorEq] at unfinished
    | div => simp only [run,parsed,resumed,reduceCtorEq] at unfinished
    | ok reply => cases reply with
      | Err e => simp only [run,parsed,resumed,reduceCtorEq] at unfinished
      | Ok pair => exact ⟨v,pair.1,pair.2,parsed,resumed⟩
#print axioms weak
#print axioms remaining
end AspisR1.NNH_064Prefix
