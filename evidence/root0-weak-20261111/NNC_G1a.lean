import NNC_WriteFree
set_option autoImplicit false
noncomputable section
namespace NNC_G1a
open Aeneas Aeneas.Std AspisR1 VTop_Stages NLW_Full064
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open RSL.TAS
/-- Canonical verifier error carrier; all other library fields remain explicit. -/
def base (debug : verifier.Error → String) (root0 : RSL.Bytes → RSL.Bytes → Prop)
 (auth : RSL.Bytes → RSL.Bytes → RSL.Bytes → RSL.Spec (Except verifier.Error Unit)) :
 RSL.TX2_241.V2Lib := ⟨verifier.Error,debug,root0,auth⟩

/-- Complete observation association, NOT an own-input clause or a proved
native root. The host interpreter must supply this for actual f064, with
exact native arguments, Result, and ordered effects (also abort prefixes). -/
def NativeRep {Ambient X : Type} (H : Bytes → State)
 (d : aspis_core.digest.Digest32 X) (hash : X) (world : NLM_PacketTypes.World Ambient)
 (r : NNC_WriteFree.Renderer Ambient X H)
 (f : RSL.Bytes → RSL.Bytes → RSL.Bytes → RSL.Env → RSL.Obs (Except verifier.Error Unit)) : Prop :=
 ∀ pub proof ck env, proof.length=57607 → ck.length=1768 → pub.length≤1880 →
 ∃ (pu pr cp : Slice U8),
  NNC_ByteCarriers.host pu.val=pub ∧ NNC_ByteCarriers.host pr.val=proof ∧
  NNC_ByteCarriers.host cp.val=ck ∧
  ∃ outcome events, NMN_064.Native H ⟨⟨d,pu,pr,cp,hash⟩,world⟩ outcome events ∧
   f pub proof ck env =
    ⟨NNC_WeakSpec.exit H _ outcome,NNC_WriteFree.render r ⟨⟨d,pu,pr,cp,hash⟩,world⟩ outcome events env⟩

/-- An exact TAS G1a fold. NativeRep and headerRep are representation
installation obligations, never claimed as discharged by this constructor. -/
def assemble {Ambient X : Type} (S : Sig) (L : RSL.PoolLib) (VL : RSL.VLib)
 (debug : verifier.Error → String) (root0 : RSL.Bytes → RSL.Bytes → Prop)
 (auth : RSL.Bytes → RSL.Bytes → RSL.Bytes → RSL.Spec (Except verifier.Error Unit))
 (I : Impl L (base debug root0 auth) VL)
 (H : Bytes → State) (d : aspis_core.digest.Digest32 X) (hash : X)
 (world : NLM_PacketTypes.World Ambient) (r : NNC_WriteFree.Renderer Ambient X H)
 (nativeRep : NativeRep H d hash world r I.f064)
 (oracle : CheckpointBytes5Inputs.Oracle (VTop_Checkpoint.digest d) hash H)
 (headerRep : ∀ env pub proof ck,
  (NLW_ReaderHeader.decode (NNC_ByteCarriers.protocol ck)=
   some (H (NNC_ByteCarriers.protocol proof),H (NNC_ByteCarriers.protocol pub))) ↔
  S.readerHeader env pub proof ck) : NNC_G1a S L (base debug root0 auth) VL I where
 w := NNC_WriteFree.law H d hash world r
 weak := by
  intro x env domain
  obtain ⟨hp,hc,hu,_⟩ := domain
  exact nativeRep x.1 x.2.1 x.2.2 env hp hc hu
 writeFree := NNC_WriteFree.writeFree H d hash world r
 okHeader := by
  intro pub proof ck env o domain observed accepted
  obtain ⟨hp,hc,hu,_⟩ := domain
  apply (headerRep env pub proof ck).mp
  have same : o=⟨.ret (.ok ()),o.events⟩ := by cases o; simp_all
  rw [same] at observed
  exact NNC_WeakSpec.accepted_header H d hash world (NNC_WriteFree.render r)
   pub proof ck hp hc hu oracle env o.events observed

#print assemble
#print axioms assemble
end NNC_G1a
