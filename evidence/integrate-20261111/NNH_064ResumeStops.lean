import NNH_064ResumeCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_064ResumeStops
open Aeneas Aeneas.Std VTop_Stages NLW_Full064
open NLT_NativeInvocation NNH_064ResumeRecord

theorem fail_common (env : RSL.Env) (r : NP6_StdModel.Reservation) (pub proof ck : Slice U8)
 (error : Error) (stopped : NNH_064ResumeError.reply env r pub proof ck=.fail error) :
 NLT_CompleteRoot.Native (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env)
 pub proof ck () (.resolved (.fail error) [record env r pub proof ck]) := by
 change Invocation _ _ _ (NKE_Free.Program.call (NKE_CommonCodec.resume ck proof pub) _ _) _ _
 refine Invocation.call_fail _ _ _ (record env r pub proof ck) rfl error ?_
 rw [NNH_064ResumeError.decoded,stopped]

theorem div_common (env : RSL.Env) (r : NP6_StdModel.Reservation) (pub proof ck : Slice U8)
 (stopped : NNH_064ResumeError.reply env r pub proof ck=.div) :
 NLT_CompleteRoot.Native (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env)
 pub proof ck () (.resolved .div [record env r pub proof ck]) := by
 change Invocation _ _ _ (NKE_Free.Program.call (NKE_CommonCodec.resume ck proof pub) _ _) _ _
 refine Invocation.call_div _ _ _ (record env r pub proof ck) rfl ?_
 rw [NNH_064ResumeError.decoded,stopped]

/-- Internal structural composition. Its native premise is supplied below by
an actual first-call stop constructor, never by choosing an admitted Spec. -/
theorem enter {Ambient : Type} (env : RSL.Env) (r : NP6_StdModel.Reservation)
 (pub proof ck : Slice U8) (world : NLM_PacketTypes.World Ambient)
 (variant : transport.Variant) (parsed : NLE_ParseInstall.parse proof=.ok (.Ok variant))
 (result : Result (core.result.Result Unit verifier.Error))
 (common : NLT_CompleteRoot.Native (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env)
 pub proof ck () (.resolved result [record env r pub proof ck])) :
 NNC_ObservedLaw.w (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env) () world
  (LIB_Carriers.bytes pub) (LIB_Carriers.bytes proof) (LIB_Carriers.bytes ck) env
  ⟨NNC_WeakSpec.resultExit result,NNC_DigestTrace.render (trace env r pub proof ck)⟩ := by
 let frame : Frame Ambient Unit := ⟨⟨LIBB_PartitionEnv.digest env,pub,proof,ck,()⟩,world⟩
 have run := NMN_064.Native.observed (H := LIBB_PartitionEnv.H env) (s := frame)
  (NLE_ParseInstall.parse proof) (fun _ => .resolved result [record env r pub proof ck])
  (LIBB_Tx2EnvCode.parser proof) (fun _ _ => common)
 rw [parsed] at run
 refine ⟨pub,proof,ck,rfl,rfl,rfl,.common (.resolved result [record env r pub proof ck]),
  _,trace env r pub proof ck,run,NNH_064ResumeNative.source env r pub proof ck,rfl⟩

/-- Actual fail carries its digest prefix only, with no successful child or
post-abort state fabricated. Parser success is just the entered branch. -/
theorem fail {Ambient : Type} (env : RSL.Env) (r : NP6_StdModel.Reservation)
 (pub proof ck : Slice U8) (world : NLM_PacketTypes.World Ambient)
 (variant : transport.Variant) (parsed : NLE_ParseInstall.parse proof=.ok (.Ok variant))
 (error : Error) (stopped : NNH_064ResumeError.reply env r pub proof ck=.fail error) :
 NNC_ObservedLaw.w (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env) () world
  (LIB_Carriers.bytes pub) (LIB_Carriers.bytes proof) (LIB_Carriers.bytes ck) env
  ⟨.abort,NNC_DigestTrace.render (trace env r pub proof ck)⟩ :=
 enter env r pub proof ck world variant parsed (.fail error)
  (fail_common env r pub proof ck error stopped)

theorem diverge {Ambient : Type} (env : RSL.Env) (r : NP6_StdModel.Reservation)
 (pub proof ck : Slice U8) (world : NLM_PacketTypes.World Ambient)
 (variant : transport.Variant) (parsed : NLE_ParseInstall.parse proof=.ok (.Ok variant))
 (stopped : NNH_064ResumeError.reply env r pub proof ck=.div) :
 NNC_ObservedLaw.w (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env) () world
  (LIB_Carriers.bytes pub) (LIB_Carriers.bytes proof) (LIB_Carriers.bytes ck) env
  ⟨.diverge,NNC_DigestTrace.render (trace env r pub proof ck)⟩ :=
 enter env r pub proof ck world variant parsed .div (div_common env r pub proof ck stopped)

#print axioms fail_common
#print axioms div_common
#print axioms enter
#print axioms fail
#print axioms diverge
end AspisR1.NNH_064ResumeStops
