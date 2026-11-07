import NNH_Entry241
import NNC_ObservedLaw
set_option autoImplicit false
noncomputable section
namespace NNH_WeakEntryNative
open Aeneas Aeneas.Std AspisR1 VTop_Stages
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open RSL NNH_Libraries

/-- SAME accepted actual241 observation, its snapshot/read cuts and the native
064 witness produced by the unchanged weak law. No native child success is
an input. Association with the headline's own recorder is a separate step. -/
structure Packet {Ambient X : Type} (H : AspisV8R19.DuplexFrames.Bytes → State)
 (d : aspis_core.digest.Digest32 X) (hash : X) (world : NLM_PacketTypes.World Ambient)
 (I0 : TAS.Impl L V0 VL) (a : TX2_240.Args) (env : Env) where
 owned : List OwnedAccount
 stageEvents : List RSL.Event
 actual : I0.f241 ⟨a.program_id,owned,a.data,env.clock⟩ env=⟨.ret (.ok ()),stageEvents⟩
 reads : NNH_RSLReads.Cut (LIBB_V2Star.weak H d hash world) ⟨a.program_id,owned,a.data,env.clock⟩ env
 publicBytes : Slice U8
 proof : Slice U8
 checkpoint : Slice U8
 public_eq : NNC_ByteCarriers.host publicBytes.val=reads.publicBytes
 proof_eq : NNC_ByteCarriers.host proof.val=
  RSL.slice reads.proofData RSL.AFTERSTATE_BYTES (RSL.AFTERSTATE_BYTES+reads.n)
 checkpoint_eq : NNC_ByteCarriers.host checkpoint.val=reads.checkpointData
 domain : NNC_064Weak.Domain (NLW_Full064.Args.mk d publicBytes proof checkpoint hash)
 records : List (NLT_NativeInvocation.Occurrence H d hash)
 events : List (NLW_Full064.Event Ambient X)
 native : NMN_064.Native H ⟨⟨d,publicBytes,proof,checkpoint,hash⟩,world⟩
  (.common (.resolved (Aeneas.Std.Result.ok (.Ok ())) records)) events
 trace : NNC_DigestTrace.Trace
 source : NNC_RecordTrace.Records records trace
 rendered : reads.verifyEvents=NNC_DigestTrace.render trace

/-- Actual entry -> actual241 -> weak-native064. The row is exactly the
library-parametric241 child field; no canonical Root0 hypothesis is used. -/
theorem produce {Ambient X : Type} (H : AspisV8R19.DuplexFrames.Bytes → State)
 (d : aspis_core.digest.Digest32 X) (hash : X) (world : NLM_PacketTypes.World Ambient)
 (I0 : TAS.Impl L V0 VL) (alloc1 alloc2 : NMV_ConcreteWindows.Allocation)
 (row : TX2_241.RowSpec_241 L D (LIBB_V2Star.weak H d hash world) I0.f241)
 (a : TX2_240.Args) (s post : SdkState) (env : Env) (route : TAS.ASQ8 a.data)
 (accepted : ((NNH_InstalledImpl.install I0 alloc1 alloc2).entry a s env).exit=.ret (.ok (),post)) :
 Nonempty (Packet H d hash world I0 a env) := by
 obtain ⟨xs,es,actual,law⟩ := NNH_Entry241.weak I0 alloc1 alloc2
  (NNC_ObservedLaw.w H d hash world) row a s post env route accepted
 obtain ⟨c⟩ := NNH_RSLReads.from_reference L D (LIBB_V2Star.weak H d hash world)
  ⟨a.program_id,xs,a.data,env.clock⟩ env es law
 obtain ⟨pu,pr,cp,hpu,hpr,hcp,outcome,events,trace,native,source,equal⟩ := c.verified
 have success : NNC_WeakSpec.exit H _ outcome=.ret (.ok ()) :=
  (congrArg Obs.exit equal).symm
 obtain ⟨records,rfl⟩ := NNC_WeakSpec.exit_ok H _ outcome success
 have proofExtent : pr.val.length=57607 := by
  simpa only [←hpr,NNC_ByteCarriers.host,List.length_map,RSL.PROOF_BYTES] using c.domain.1
 have ckExtent : cp.val.length=1768 := by
  simpa only [←hcp,NNC_ByteCarriers.host,List.length_map,RSL.CHECKPOINT_BYTES] using c.domain.2.1
 have publicBound : pu.val.length≤1880 := by
  simpa only [←hpu,NNC_ByteCarriers.host,List.length_map,RSL.STATEMENT_BYTES] using c.domain.2.2.1
 exact ⟨⟨xs,es,actual,c,pu,pr,cp,hpu,hpr,hcp,⟨proofExtent,ckExtent,publicBound⟩,
  records,events,native,trace,source,congrArg Obs.events equal⟩⟩

#print axioms produce
end NNH_WeakEntryNative
