import NNH_ReaderHeaderEnv
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_064EnvHeader
open Aeneas Aeneas.Std Result VTop_Stages NLW_Full064
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical

theorem resume (env : RSL.Env) (r : NP6_StdModel.Reservation)
 (pub proof ck : Slice U8) (length : ck.val.length=1768)
 (p : verifier.Prepared) (a : verifier.Accumulator)
 (resumed : NJJ_Common.resume r (LIBB_PartitionEnv.digest env) ck proof pub .S2 ()=.ok (.Ok (p,a))) :
 NLW_ReaderHeader.decode (bytesOf ck.val)=
 some (LIBB_HashModel.H env (bytesOf proof.val),LIBB_HashModel.H env (bytesOf pub.val)) := by
 unfold NJJ_Common.resume at resumed
 rw [NJC_ResumeCalls.clause] at resumed
 have same := NKE_ResumeDomain.action_ok _ _ resumed
 obtain ⟨calls⟩:=CheckpointBytes4Comparison.successful_calls (NJC_FilledClause.reserved r)
  (NJC_ResumeCalls.digest (LIBB_PartitionEnv.digest env)) ck proof pub .S2 () p a same
 exact NNH_ReaderHeaderEnv.calls env ck proof pub calls length

theorem native {Ambient : Type} (env : RSL.Env)
 (pub proof ck : Slice U8) (world : NLM_PacketTypes.World Ambient)
 (domain : NNC_064Weak.Domain
  (⟨LIBB_PartitionEnv.digest env,pub,proof,ck,()⟩ : Args Unit))
 (records : List (NLT_NativeInvocation.Occurrence (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env) ()))
 (events : List (Event Ambient Unit))
 (source : NMN_064.Native (LIBB_PartitionEnv.H env)
  ⟨⟨LIBB_PartitionEnv.digest env,pub,proof,ck,()⟩,world⟩
  (.common (.resolved (.ok (.Ok ())) records)) events) :
 NLW_ReaderHeader.decode (bytesOf ck.val)=
 some (LIBB_HashModel.H env (bytesOf proof.val),LIBB_HashModel.H env (bytesOf pub.val)) := by
 have law := (NNC_064Weak.root (LIBB_PartitionEnv.H env) _ domain).1 _ _ source
 obtain ⟨p,a,resumed⟩ := NNC_ResumeHeader.resume_of_ok _ _ _ _ (LIBB_PartitionEnv.digest env)
  pub proof ck () law.1.1.symm
 exact resume env _ pub proof ck domain.checkpointExtent p a resumed

#print axioms resume
#print axioms native
end AspisR1.NNH_064EnvHeader
