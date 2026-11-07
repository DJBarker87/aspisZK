import NNH_064ResumeError
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_064ResumeNative
open Aeneas Aeneas.Std VTop_Stages NLW_Full064
open NNH_064ResumeRecord

theorem native {Ambient : Type} (env : RSL.Env) (r : NP6_StdModel.Reservation)
 (pub proof ck : Slice U8) (world : NLM_PacketTypes.World Ambient)
 (variant : transport.Variant) (parsed : NLE_ParseInstall.parse proof=.ok (.Ok variant))
 (error : verifier.Error) (returned : NNH_064ResumeError.reply env r pub proof ck=.ok (.Err error)) :
 NMN_064.Native (LIBB_PartitionEnv.H env)
  ⟨⟨LIBB_PartitionEnv.digest env,pub,proof,ck,()⟩,world⟩
  (.common (.resolved (.ok (.Err error)) [record env r pub proof ck]))
  [.parse ⟨⟨LIBB_PartitionEnv.digest env,pub,proof,ck,()⟩,world⟩ (.ok (.Ok variant)),
   .marker ⟨⟨LIBB_PartitionEnv.digest env,pub,proof,ck,()⟩,world⟩,
   .commonEnter ⟨⟨LIBB_PartitionEnv.digest env,pub,proof,ck,()⟩,world⟩] := by
 have source := NMN_064.Native.observed
  (H := LIBB_PartitionEnv.H env)
  (s := (⟨⟨LIBB_PartitionEnv.digest env,pub,proof,ck,()⟩,world⟩ : Frame Ambient Unit))
  (NLE_ParseInstall.parse proof) (fun _ => .resolved (.ok (.Err error)) [record env r pub proof ck])
  (LIBB_Tx2EnvCode.parser proof)
  (fun _ _ => NNH_064ResumeError.common env r pub proof ck error returned)
 simpa only [parsed,NMN_OracleFold.run] using source

theorem source (env : RSL.Env) (r : NP6_StdModel.Reservation) (pub proof ck : Slice U8) :
 NNC_RecordTrace.Records [record env r pub proof ck] (trace env r pub proof ck) := by
 simpa only [List.append_nil] using NNC_RecordTrace.Records.cons
  (record env r pub proof ck) [] (trace env r pub proof ck) []
  (from_record env r pub proof ck) NNC_RecordTrace.Records.nil

/-- Exact weak observation of the entered-source resume-error branch. No
Root0, child success or source observation witness is assumed. -/
theorem weak {Ambient : Type} (env : RSL.Env) (r : NP6_StdModel.Reservation)
 (pub proof ck : Slice U8) (world : NLM_PacketTypes.World Ambient)
 (variant : transport.Variant) (parsed : NLE_ParseInstall.parse proof=.ok (.Ok variant))
 (error : verifier.Error) (returned : NNH_064ResumeError.reply env r pub proof ck=.ok (.Err error)) :
 NNC_ObservedLaw.w (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env) () world
  (LIB_Carriers.bytes pub) (LIB_Carriers.bytes proof) (LIB_Carriers.bytes ck) env
  ⟨.ret (.error error),NNC_DigestTrace.render (trace env r pub proof ck)⟩ := by
 refine ⟨pub,proof,ck,rfl,rfl,rfl,.common (.resolved (.ok (.Err error)) [record env r pub proof ck]),
  _,trace env r pub proof ck,native env r pub proof ck world variant parsed error returned,
  source env r pub proof ck,rfl⟩

#print axioms native
#print axioms source
#print axioms weak
end AspisR1.NNH_064ResumeNative
