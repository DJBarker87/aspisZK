import NNC_ObservedWeak
import TAS_Interfaces
set_option autoImplicit false
noncomputable section
namespace NNC_ObservedLaw
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NLW_Full064
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- The concrete Root0-free weak 064 law in V2Lib.tx2auth's exact shape.
There is no arbitrary renderer: observed events are the native resume/C04
trace decoration, and failed/pending native calls remain in the witness. -/
def w {Ambient X : Type} (H : Bytes → State) (d : aspis_core.digest.Digest32 X)
 (hash : X) (world : NLM_PacketTypes.World Ambient)
 (pub proof ck : RSL.Bytes) : RSL.Spec (Except verifier.Error Unit) :=
 fun _ observed => ∃ (pu pr cp : Slice U8),
 NNC_ByteCarriers.host pu.val=pub ∧ NNC_ByteCarriers.host pr.val=proof ∧
 NNC_ByteCarriers.host cp.val=ck ∧
 NNC_ObservedWeak.Observed H ⟨⟨d,pu,pr,cp,hash⟩,world⟩ observed

theorem contains_native {Ambient X : Type} (H : Bytes → State) (s : Frame Ambient X)
 (domain : NNC_064Weak.Domain s.args) (outcome : End H s.args)
 (events : List (Event Ambient X)) (native : NMN_064.Native H s outcome events) (env : RSL.Env) :
 ∃ observed, w H s.args.digest s.args.hash s.world
   (NNC_ByteCarriers.host s.args.publicBytes.val) (NNC_ByteCarriers.host s.args.proof.val)
   (NNC_ByteCarriers.host s.args.checkpoint.val) env observed ∧
   observed.exit=NNC_WeakSpec.exit H s.args outcome := by
 obtain ⟨_,_,trace,source,observed⟩ := NNC_ObservedWeak.transport H s domain outcome events native
 exact ⟨_,⟨s.args.publicBytes,s.args.proof,s.args.checkpoint,rfl,rfl,rfl,observed⟩,rfl⟩

theorem writeFree {Ambient X : Type} (H : Bytes → State) (d : aspis_core.digest.Digest32 X)
 (hash : X) (world : NLM_PacketTypes.World Ambient) (pub proof ck : RSL.Bytes) :
 RSL.TAS.WriteFree (w H d hash world pub proof ck) := by
 intro env observed source c b
 obtain ⟨pu,pr,cp,_,_,_,native⟩ := source
 exact NNC_ObservedWeak.no_write H _ observed native c b

theorem accepted_header {Ambient X : Type} (H : Bytes → State) (d : aspis_core.digest.Digest32 X)
 (hash : X) (world : NLM_PacketTypes.World Ambient) (pub proof ck : RSL.Bytes)
 (proofLength : proof.length=57607) (checkpointLength : ck.length=1768) (publicBound : pub.length≤1880)
 (oracle : CheckpointBytes5Inputs.Oracle (VTop_Checkpoint.digest d) hash H)
 (env : RSL.Env) (observed : RSL.Obs (Except verifier.Error Unit))
 (native : w H d hash world pub proof ck env observed) (ok : observed.exit=.ret (.ok ())) :
 NLW_ReaderHeader.decode (NNC_ByteCarriers.protocol ck)=
 some (H (NNC_ByteCarriers.protocol proof),H (NNC_ByteCarriers.protocol pub)) := by
 obtain ⟨pu,pr,cp,hpu,hpr,hcp,native⟩ := native
 have puLen : pu.val.length≤1880 := by simpa only [←hpu,NNC_ByteCarriers.host,List.length_map] using publicBound
 have prLen : pr.val.length=57607 := by simpa only [←hpr,NNC_ByteCarriers.host,List.length_map] using proofLength
 have cpLen : cp.val.length=1768 := by simpa only [←hcp,NNC_ByteCarriers.host,List.length_map] using checkpointLength
 have header := NNC_ObservedWeak.accepted_header H ⟨⟨d,pu,pr,cp,hash⟩,world⟩
   ⟨prLen,cpLen,puLen⟩ oracle observed native ok
 rw [←hcp,←hpr,←hpu,NNC_ByteCarriers.protocol_host,NNC_ByteCarriers.protocol_host,
   NNC_ByteCarriers.protocol_host]
 exact header

#print axioms contains_native
#print axioms writeFree
#print axioms accepted_header
end NNC_ObservedLaw
