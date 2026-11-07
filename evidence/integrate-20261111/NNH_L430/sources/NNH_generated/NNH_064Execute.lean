import NNH_064CommonTrace
import NNH_064Parser
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_064Execute
open Aeneas Aeneas.Std VTop_Stages NLW_Full064

def common (env : RSL.Env) (pub proof ck : Slice U8) :=
 NLT_CompleteRoot.End.resolved
  (NKE_Free.eval (NNH_064CommonRecords.program env pub proof ck)).result
  (NNH_064CommonRecords.records env pub proof ck)

def outcome (env : RSL.Env) (pub proof ck : Slice U8) :
 End (LIBB_PartitionEnv.H env) (⟨LIBB_PartitionEnv.digest env,pub,proof,ck,()⟩ : Args Unit) :=
 match NLE_ParseInstall.parse proof with
 | .fail e => .parseFail e
 | .div => .parseDiv
 | .ok (.Err e) => .parseReject e
 | .ok (.Ok _) => .common (common env pub proof ck)

def trace (env : RSL.Env) (pub proof ck : Slice U8) : NNC_DigestTrace.Trace :=
 match NLE_ParseInstall.parse proof with
 | .ok (.Ok _) => NNH_064CommonTrace.trace env pub proof ck
 | _ => []

def observation (env : RSL.Env) (pub proof ck : Slice U8) : RSL.Obs (Except verifier.Error Unit) :=
 ⟨NNC_WeakSpec.exit (LIBB_PartitionEnv.H env) _ (outcome env pub proof ck),
  NNC_DigestTrace.render (trace env pub proof ck)⟩

/-- Every reached source continuation is executed. The only size used here
is the original064 own-input extent; no child-success or Root0 premise. -/
theorem native {Ambient : Type} (env : RSL.Env) (pub proof ck : Slice U8)
 (world : NLM_PacketTypes.World Ambient) (len : proof.val.length=57607) :
 ∃ events, NMN_064.Native (LIBB_PartitionEnv.H env)
  ⟨⟨LIBB_PartitionEnv.digest env,pub,proof,ck,()⟩,world⟩ (outcome env pub proof ck) events := by
 have run := NMN_064.Native.observed
  (H := LIBB_PartitionEnv.H env)
  (s := (⟨⟨LIBB_PartitionEnv.digest env,pub,proof,ck,()⟩,world⟩ : Frame Ambient Unit))
  (NLE_ParseInstall.parse proof) (fun _=>common env pub proof ck)
  (LIBB_Tx2EnvCode.parser proof) (fun _ _=>NNH_064CommonRecords.skeleton env pub proof ck len)
 refine ⟨_,?_⟩
 cases parsed : NLE_ParseInstall.parse proof with
 | fail e => simpa only [outcome,parsed,NMN_OracleFold.run] using run
 | div => simpa only [outcome,parsed,NMN_OracleFold.run] using run
 | ok reply => cases reply with
   | Err e => simpa only [outcome,parsed,NMN_OracleFold.run] using run
   | Ok v => simpa only [outcome,parsed,NMN_OracleFold.run] using run

#print axioms native
end AspisR1.NNH_064Execute
