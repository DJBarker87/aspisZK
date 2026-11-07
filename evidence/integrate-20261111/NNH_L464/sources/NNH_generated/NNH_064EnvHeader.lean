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
 (s : Frame Ambient Unit) (d : s.args.digest=LIBB_PartitionEnv.digest env)
 (hash : s.args.hash=()) (domain : NNC_064Weak.Domain s.args)
 (records : List (NLT_NativeInvocation.Occurrence (LIBB_PartitionEnv.H env) s.args.digest s.args.hash))
 (events : List (Event Ambient Unit))
 (source : NMN_064.Native (LIBB_PartitionEnv.H env) s
  (.common (.resolved (.ok (.Ok ())) records)) events) :
 NLW_ReaderHeader.decode (bytesOf s.args.checkpoint.val)=
 some (LIBB_HashModel.H env (bytesOf s.args.proof.val),LIBB_HashModel.H env (bytesOf s.args.publicBytes.val)) := by
 have law := (NNC_064Weak.root (LIBB_PartitionEnv.H env) s domain).1 _ _ source
 obtain ⟨p,a,resumed⟩ := NNC_ResumeHeader.resume_of_ok _ _ _ _ s.args.digest
  s.args.publicBytes s.args.proof s.args.checkpoint s.args.hash law.1.1.symm
 rw [d,hash] at resumed
 exact resume env _ s.args.publicBytes s.args.proof s.args.checkpoint domain.checkpointExtent p a resumed
#print axioms resume
#print axioms native
end AspisR1.NNH_064EnvHeader
