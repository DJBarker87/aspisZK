import NNH_EnvEntryNative
import NNH_064World
set_option autoImplicit false
noncomputable section
namespace NNH_EnvEntryWorld
open Aeneas Aeneas.Std AspisR1 RSL NNH_Libraries
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Preserve the entered064 arguments, endpoint and every native record when
rebuilding its external annotation at the physical caller frame. -/
theorem native {A : Type} (I0 : TAS.Impl L V0 VL) (a : TX2_240.Args) (env : Env)
 (packet : NNH_EnvEntryNative.Packet I0 a env) (world : NLM_PacketTypes.World A) :
 ∃ events, NMN_064.Native (LIBB_PartitionEnv.H env)
  ⟨⟨LIBB_PartitionEnv.digest env,packet.publicBytes,packet.proof,packet.checkpoint,()⟩,world⟩
  (.common (.resolved (Aeneas.Std.Result.ok (.Ok ())) packet.records)) events := by
 exact NNH_064World.transport (LIBB_PartitionEnv.H env) _ world _ _ packet.native
#print axioms native
end NNH_EnvEntryWorld
