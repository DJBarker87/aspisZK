import NNP_ResumeHeader
set_option autoImplicit false
noncomputable section
namespace NNP_SeparateHeader
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NLW_Full064
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical

/-- Separate resume-header hash; the weak law's C04 model is unchanged. -/
def header (env : RSL.Env) (pub proof ck : RSL.Bytes) : Prop :=
 NLW_ReaderHeader.decode (NNC_ByteCarriers.protocol ck) =
 some (LIBB_HashModel.H env (NNC_ByteCarriers.protocol proof),
       LIBB_HashModel.H env (NNC_ByteCarriers.protocol pub))

/-- No oracle or repartitioning premise: the actual resume singleton replies
are interpreted at the same Env as the native C04 model. -/
theorem okHeader {Ambient : Type} (world : NLM_PacketTypes.World Ambient)
 (pub proof ck : RSL.Bytes) (env : RSL.Env) (o : RSL.Obs (Except LIBW_WeakPerEnv.LibErr Unit))
 (domain : RSL.TX2_241.Dom064 (LIBW_WeakPerEnv.weakEnv world) (pub,proof,ck))
 (observed : LIBW_WeakPerEnv.wEnv world pub proof ck env o)
 (ok : o.exit = .ret (.ok ())) : header env pub proof ck := by
 obtain ⟨hp,hc,hu,_⟩ := domain
 obtain ⟨pu,pr,cp,hpu,hpr,hcp,outcome,events,trace,native,source,same⟩ := observed
 have accepted : NNC_WeakSpec.exit (LIBB_PartitionEnv.H env) _ outcome = .ret (.ok ()) := by
  rw [same] at ok
  exact ok
 obtain ⟨records,rfl⟩ := NNC_WeakSpec.exit_ok _ _ outcome accepted
 have puLen : pu.val.length ≤ 1880 := by
  simpa only [←hpu,NNC_ByteCarriers.host,List.length_map,RSL.STATEMENT_BYTES] using hu
 have prLen : pr.val.length = 57607 := by
  simpa only [←hpr,NNC_ByteCarriers.host,List.length_map,RSL.PROOF_BYTES] using hp
 have cpLen : cp.val.length = 1768 := by
  simpa only [←hcp,NNC_ByteCarriers.host,List.length_map,RSL.CHECKPOINT_BYTES] using hc
 have h := NNH_064EnvHeader.native env pu pr cp world ⟨prLen,cpLen,puLen⟩ records events native
 unfold header
 rw [←hcp,←hpr,←hpu,NNC_ByteCarriers.protocol_host,NNC_ByteCarriers.protocol_host,
  NNC_ByteCarriers.protocol_host]
 exact h

theorem okHeader_any (Ambient : Type)
 (pub proof ck : RSL.Bytes) (env : RSL.Env) (o : RSL.Obs (Except LIBW_WeakPerEnv.LibErr Unit))
 (domain : RSL.TX2_241.Dom064 (LIBW_WeakPerEnv.weakAny Ambient) (pub,proof,ck))
 (observed : LIBW_WeakPerEnv.wAny Ambient pub proof ck env o)
 (ok : o.exit = .ret (.ok ())) : header env pub proof ck := by
 obtain ⟨world,h⟩ := observed
 exact okHeader world pub proof ck env o domain h ok

/-- Canonical native's OWN hypotheses imply the separate-header fact at that
same Env on returned success; bound/trace are retained verbatim, not strengthened. -/
theorem canonical_header {Ambient : Type} (env : RSL.Env) (pub proof ck : Slice U8)
 (world : NLM_PacketTypes.World Ambient)
 (domain : LIBB_Tx2Domain.domain (LIB_Carriers.bytes pub) (LIB_Carriers.bytes proof) (LIB_Carriers.bytes ck))
 (outcome : NLW_Full064.End (LIBB_PartitionEnv.H env)
  (⟨LIBB_PartitionEnv.digest env,pub,proof,ck,()⟩ : NLW_Full064.Args Unit))
 (events : List (NLW_Full064.Event Ambient Unit))
 (invocation : NMN_064.Native (LIBB_PartitionEnv.H env)
  ⟨⟨LIBB_PartitionEnv.digest env,pub,proof,ck,()⟩,world⟩ outcome events)
 (_bound : LIBB_ObservationFold.Bound064 env pub proof ck outcome) (trace : NNC_DigestTrace.Trace)
 (_source : NNC_ObservedWeak.TraceOf outcome trace)
 (accepted : NNC_WeakSpec.exit (LIBB_PartitionEnv.H env) _ outcome = .ret (.ok ())) :
 NLW_ReaderHeader.decode (bytesOf ck.val) =
 some (LIBB_HashModel.H env (bytesOf proof.val),LIBB_HashModel.H env (bytesOf pub.val)) := by
 have own := (LIBB_Tx2Domain.native env pub proof ck).mp domain
 obtain ⟨records,rfl⟩ := NNC_WeakSpec.exit_ok _ _ outcome accepted
 exact NNH_064EnvHeader.native env pub proof ck world
  ⟨own.proofExtent,own.checkpointExtent,own.publicBound⟩ records events invocation

/-- The TAS field requires only the host's explicit representation of its
chosen header predicate. No additional premise is placed on HostRep. -/
theorem okHeader_field {Ambient : Type} (S : RSL.TAS.Sig)
 (world : NLM_PacketTypes.World Ambient)
 (headerRep : ∀ env pub proof ck, header env pub proof ck → S.readerHeader env pub proof ck) :
 ∀ pub proof ck env (o : RSL.Obs (Except LIBW_WeakPerEnv.LibErr Unit)),
 RSL.TX2_241.Dom064 (LIBW_WeakPerEnv.weakEnv world) (pub,proof,ck) →
 LIBW_WeakPerEnv.wEnv world pub proof ck env o → o.exit = .ret (.ok ()) →
 S.readerHeader env pub proof ck :=
 fun pub proof ck env o domain observed ok =>
 headerRep env pub proof ck (okHeader world pub proof ck env o domain observed ok)

#print axioms okHeader
#print axioms okHeader_any
#print axioms canonical_header
#print axioms okHeader_field
end NNP_SeparateHeader
