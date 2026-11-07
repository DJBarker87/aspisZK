import NNH_064ResumeNative
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_064ResumeCanonical
open Aeneas Aeneas.Std VTop_Stages NLW_Full064
open NNH_064ResumeRecord NNH_Libraries
/-- Canonical and weak interpretations agree on the SAME constructed native
resume-error execution. The canonical domain is unchanged, and reservation
agreement is runtime representation, not a new caller clause. -/
theorem canonical {Ambient : Type}
 (sha : List RSL.Bytes → RSL.B32) (pda : List RSL.Bytes → RSL.B32 → Option RSL.B32)
 (clock : Except RSL.ProgramError UInt64) (r : NP6_StdModel.Reservation)
 (env : RSL.Env) (rep : NNH_HostEnv.EnvRep sha pda clock r env)
 (pub proof ck : Slice U8) (world : NLM_PacketTypes.World Ambient)
 (domain : RSL.TX2_241.Dom064 V0 (LIB_Carriers.bytes pub,LIB_Carriers.bytes proof,LIB_Carriers.bytes ck))
 (variant : transport.Variant) (parsed : NLE_ParseInstall.parse proof=.ok (.Ok variant))
 (error : verifier.Error) (returned : NNH_064ResumeError.reply env r pub proof ck=.ok (.Err error)) :
 V0.tx2auth (LIB_Carriers.bytes pub) (LIB_Carriers.bytes proof) (LIB_Carriers.bytes ck) env
  ⟨.ret (.error error),NNC_DigestTrace.render (trace env r pub proof ck)⟩ := by
 have run := NNH_064ResumeNative.native env r pub proof ck world variant parsed error returned
 have bound : LIBB_ObservationFold.Bound064 env pub proof ck
  (.common (.resolved (.ok (.Err error)) [record env r pub proof ck])) := by
  intro rec member
  have same := List.mem_singleton.mp member
  subst rec
  exact NNH_064ResumeRecord.bound sha pda clock r env rep pub proof ck
 exact (LIBB_Tx2Auth.native env pub proof ck world domain _ _ run bound
  (trace env r pub proof ck) (NNH_064ResumeNative.source env r pub proof ck)).2.2
#print axioms canonical
end AspisR1.NNH_064ResumeCanonical
