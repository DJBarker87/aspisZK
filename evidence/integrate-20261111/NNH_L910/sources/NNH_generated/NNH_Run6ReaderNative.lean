import NNH_WeakReaderCuts
import NNT_G1aLaw
import NNH_PhysicalCarriers
import NNH_ByteListInjective
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run6ReaderNative
open Aeneas Aeneas.Std Result NND_Carrier NNH_ModelCarrier _root_.AdapterRw
open S2W_NativeConsolidation S2W_ExtractionBoundary NNH_Libraries
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem native_bytes (bs : List U8) :
 NNC_ByteCarriers.nativeList (bs.map NND_Carrier.byte) = bs := by
 induction bs with
 | nil => rfl
 | cons b bs ih =>
  change NNC_ByteCarriers.nativeByte (NND_Carrier.byte b) ::
   NNC_ByteCarriers.nativeList (bs.map NND_Carrier.byte) = b :: bs
  have roundtrip : NNC_ByteCarriers.nativeByte (NND_Carrier.byte b) = b := by rfl
  rw [roundtrip,ih]

theorem slices (x y : Slice U8) (same : NNC_ByteCarriers.host x.val = NND_Carrier.bytes y) : x = y := by
 apply Subtype.ext
 have converted := congrArg NNC_ByteCarriers.nativeList same
 rw [NNC_ByteCarriers.native_host] at converted
 exact converted.trans (native_bytes y.val)

theorem native (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (program : solana_pubkey.Pubkey) (xs : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (clock : Slot)
 (p : NNH_WeakTx2Inputs.Packet m env err r (RSL.TAS.lib V0 (fun _ _ => True) V0.tx2auth)
  program xs data clock)
 (s : SecondCut)
 (cuts : NNH_WeakReaderCuts.Facts (NNH_CorrectConfiguration.sdk m env err r) program xs data clock s)
 (raw : s.raw = p.proof) (checkpoint : s.checkpoint = p.checkpoint) (encoded : s.encoded = p.encoded) :
 ∃ records events,
  NNC_064Weak.Domain (NLW_Full064.Args.mk (LIBB_PartitionEnv.digest env) s.pub s.proof s.checkpoint ()) ∧
  NMN_064.Native (LIBB_PartitionEnv.H env)
   ⟨⟨LIBB_PartitionEnv.digest env,s.pub,s.proof,s.checkpoint,()⟩,NNH_064Install.frame⟩
   (.common (.resolved (.ok (.Ok ())) records)) events := by
 obtain ⟨pu,pr,ck,hpu,hpr,hck,domain,records,events,run⟩ :=
  NNT_G1aLaw.native_bytes_of_ok env _ _ _ NNH_064Install.frame _
   p.logical.reads.domain p.logical.reads.verified rfl
 have puEq : pu = s.pub := by
  apply slices
  rw [hpu]
  exact (by simpa only [SecondCut.pub,encoded] using p.public_eq.symm)
 have ckEq : ck = s.checkpoint := by
  apply slices
  rw [hck,checkpoint,p.checkpoint_eq]
 have n : p.logical.reads.n = 57607 := p.logical.n_eq.trans p.extent
 have prEq : pr = s.proof := by
  apply slices
  rw [hpr,cuts.proof_eq,raw,p.proof_eq,n]
  rfl
 subst pu; subst pr; subst ck
 exact ⟨records,events,domain,run⟩
#print axioms native_bytes
#print axioms slices
#print axioms native
end AspisR1.NNH_Run6ReaderNative
end
