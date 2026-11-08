import LIBW_WeakPerEnv
import NNH_064EnvHeader
set_option autoImplicit false
noncomputable section
namespace NNP_ResumeHeader
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NLW_Full064
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical

/-- Only the two header singleton replies must agree with the C04 hash model.
The checksum is consumed by resume but does not appear in the decoded header. -/
def HeaderAgreement (env : RSL.Env) (proof pub : Bytes) : Prop :=
 LIBB_HashModel.H env proof = LIBB_PartitionEnv.H env proof ∧
 LIBB_HashModel.H env pub = LIBB_PartitionEnv.H env pub

/-- The third (checksum) call requires no model value for header transport. -/
theorem resume (env : RSL.Env) (r : NP6_StdModel.Reservation)
 (pub proof ck : Slice U8) (length : ck.val.length = 1768)
 (agreement : HeaderAgreement env (bytesOf proof.val) (bytesOf pub.val))
 (p : verifier.Prepared) (a : verifier.Accumulator)
 (resumed : NJJ_Common.resume r (LIBB_PartitionEnv.digest env) ck proof pub .S2 () = .ok (.Ok (p,a))) :
 NLW_ReaderHeader.decode (bytesOf ck.val) =
 some (LIBB_PartitionEnv.H env (bytesOf proof.val), LIBB_PartitionEnv.H env (bytesOf pub.val)) := by
 have h := NNH_064EnvHeader.resume env r pub proof ck length p a resumed
 rw [agreement.1, agreement.2] at h
 exact h

/-- Same input, Env, native outcome and observation; no output premise is added. -/
theorem okHeader {Ambient : Type} (world : NLM_PacketTypes.World Ambient)
 (pub proof ck : RSL.Bytes) (env : RSL.Env) (o : RSL.Obs (Except LIBW_WeakPerEnv.LibErr Unit))
 (domain : RSL.TX2_241.Dom064 (LIBW_WeakPerEnv.weakEnv world) (pub,proof,ck))
 (observed : LIBW_WeakPerEnv.wEnv world pub proof ck env o)
 (ok : o.exit = .ret (.ok ()))
 (agreement : HeaderAgreement env (NNC_ByteCarriers.protocol proof) (NNC_ByteCarriers.protocol pub)) :
 NLW_ReaderHeader.decode (NNC_ByteCarriers.protocol ck) =
 some (LIBB_PartitionEnv.H env (NNC_ByteCarriers.protocol proof),
       LIBB_PartitionEnv.H env (NNC_ByteCarriers.protocol pub)) := by
 obtain ⟨hp,hc,hu,_⟩ := domain
 obtain ⟨pu,pr,cp,hpu,hpr,hcp,outcome,events,trace,native,source,same⟩ := observed
 have accepted : NNC_WeakSpec.exit (LIBB_PartitionEnv.H env) _ outcome = .ret (.ok ()) := by
  rw [same] at ok
  exact ok
 obtain ⟨records,rfl⟩ := NNC_WeakSpec.exit_ok _ _ outcome accepted
 have puLen : pu.val.length ≤ 1880 := by
  simpa only [←hpu,NNC_ByteCarriers.host,List.length_map] using hu
 have prLen : pr.val.length = 57607 := by
  simpa only [←hpr,NNC_ByteCarriers.host,List.length_map] using hp
 have cpLen : cp.val.length = 1768 := by
  simpa only [←hcp,NNC_ByteCarriers.host,List.length_map] using hc
 have law := (NNC_064Weak.root (LIBB_PartitionEnv.H env)
  ⟨⟨LIBB_PartitionEnv.digest env,pu,pr,cp,()⟩,world⟩ ⟨prLen,cpLen,puLen⟩).1 _ _ native
 obtain ⟨p,a,resumed⟩ := NNC_ResumeHeader.resume_of_ok _ _ _ _
  (LIBB_PartitionEnv.digest env) pu pr cp () law.1.1.symm
 rw [←hpr,←hpu,NNC_ByteCarriers.protocol_host,NNC_ByteCarriers.protocol_host] at agreement
 have h := resume env _ pu pr cp cpLen agreement p a resumed
 rw [←hcp,←hpr,←hpu,NNC_ByteCarriers.protocol_host,NNC_ByteCarriers.protocol_host,
  NNC_ByteCarriers.protocol_host]
 exact h

theorem okHeader_any (Ambient : Type)
 (pub proof ck : RSL.Bytes) (env : RSL.Env) (o : RSL.Obs (Except LIBW_WeakPerEnv.LibErr Unit))
 (domain : RSL.TX2_241.Dom064 (LIBW_WeakPerEnv.weakAny Ambient) (pub,proof,ck))
 (observed : LIBW_WeakPerEnv.wAny Ambient pub proof ck env o)
 (ok : o.exit = .ret (.ok ()))
 (agreement : HeaderAgreement env (NNC_ByteCarriers.protocol proof) (NNC_ByteCarriers.protocol pub)) :
 NLW_ReaderHeader.decode (NNC_ByteCarriers.protocol ck) =
 some (LIBB_PartitionEnv.H env (NNC_ByteCarriers.protocol proof),
       LIBB_PartitionEnv.H env (NNC_ByteCarriers.protocol pub)) := by
 obtain ⟨world,h⟩ := observed
 exact okHeader world pub proof ck env o domain h ok agreement

#print axioms resume
#print axioms okHeader
#print axioms okHeader_any
end NNP_ResumeHeader
