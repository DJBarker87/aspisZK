import NNT_G1aLaw
import NNH_Entry241
set_option autoImplicit false
noncomputable section
namespace NNT_WeakEntryLaw
open Aeneas Aeneas.Std AspisR1 VTop_Stages RSL NNH_Libraries
abbrev weak := TAS.lib V0 (fun _ _ => True) V0.tx2auth

structure Packet {Ambient : Type} (env : Env) (world : NLM_PacketTypes.World Ambient)
 (I0 : TAS.Impl L V0 VL) (a : TX2_240.Args) where
 owned : List OwnedAccount
 stageEvents : List RSL.Event
 actual : I0.f241 ⟨a.program_id,owned,a.data,env.clock⟩ env=⟨.ret (.ok ()),stageEvents⟩
 reads : NNH_RSLReads.Cut weak ⟨a.program_id,owned,a.data,env.clock⟩ env
 publicBytes : Slice U8
 proof : Slice U8
 checkpoint : Slice U8
 public_eq : NNC_ByteCarriers.host publicBytes.val=reads.publicBytes
 proof_eq : NNC_ByteCarriers.host proof.val=
  RSL.slice reads.proofData RSL.AFTERSTATE_BYTES (RSL.AFTERSTATE_BYTES+reads.n)
 checkpoint_eq : NNC_ByteCarriers.host checkpoint.val=reads.checkpointData
 domain : NNC_064Weak.Domain (NLW_Full064.Args.mk (LIBB_PartitionEnv.digest env) publicBytes proof checkpoint ())
 records : List (NLT_NativeInvocation.Occurrence (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env) ())
 events : List (NLW_Full064.Event Ambient Unit)
 native : NMN_064.Native (LIBB_PartitionEnv.H env)
  ⟨⟨LIBB_PartitionEnv.digest env,publicBytes,proof,checkpoint,()⟩,world⟩
  (.common (.resolved (.ok (.Ok ())) records)) events

theorem produce {Ambient : Type} (env : Env) (world : NLM_PacketTypes.World Ambient)
 (I0 : TAS.Impl L V0 VL) (alloc1 alloc2 : NMV_ConcreteWindows.Allocation)
 (row : TX2_241.RowSpec_241 L D weak I0.f241)
 (a : TX2_240.Args) (s post : SdkState) (route : TAS.ASQ8 a.data)
 (accepted : ((NNH_InstalledImpl.install I0 alloc1 alloc2).entry a s env).exit=.ret (.ok (),post)) :
 Nonempty (Packet env world I0 a) := by
 obtain ⟨xs,es,actual,law⟩ := NNH_Entry241.weak I0 alloc1 alloc2 V0.tx2auth row a s post env route accepted
 obtain ⟨c⟩ := NNH_RSLReads.from_reference L D weak ⟨a.program_id,xs,a.data,env.clock⟩ env es law
 obtain ⟨pu,pr,cp,hpu,hpr,hcp,domain,records,events,native⟩ :=
  NNT_G1aLaw.native_bytes_of_ok env _ _ _ world _ c.domain c.verified rfl
 exact ⟨⟨xs,es,actual,c,pu,pr,cp,hpu,hpr,hcp,domain,records,events,native⟩⟩
#print axioms produce
end NNT_WeakEntryLaw
