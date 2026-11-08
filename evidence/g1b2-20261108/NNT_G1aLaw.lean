import NNT_LawOk
import NNH_G1aEnv
set_option autoImplicit false
noncomputable section
namespace NNT_G1aLaw
open Aeneas Aeneas.Std AspisR1 VTop_Stages NNH_Libraries
open RSL.NNT

theorem native_bytes_of_ok {Ambient : Type} (env : RSL.Env) (pub pr ck : RSL.Bytes)
 (world : NLM_PacketTypes.World Ambient) (o : RSL.Obs (Except V0.VErr Unit))
 (domain : RSL.TX2_241.Dom064 (RSL.TAS.lib V0 (fun _ _ => True) V0.tx2auth) (pub,pr,ck))
 (source : V0.tx2auth pub pr ck env o) (ok : o.exit = .ret (.ok ())) :
 ∃ (pu proof cp : Slice U8),
 NNC_ByteCarriers.host pu.val=pub ∧ NNC_ByteCarriers.host proof.val=pr ∧
 NNC_ByteCarriers.host cp.val=ck ∧
 NNC_064Weak.Domain (⟨LIBB_PartitionEnv.digest env,pu,proof,cp,()⟩ : NLW_Full064.Args Unit) ∧
 ∃ records events, NMN_064.Native (LIBB_PartitionEnv.H env)
  ⟨⟨LIBB_PartitionEnv.digest env,pu,proof,cp,()⟩,world⟩
  (.common (.resolved (.ok (.Ok ())) records)) events := by
 have fits := NNH_064WeakField.fits (pub,pr,ck) domain
 change LIBB_Tx2Auth.law pub pr ck env o at source
 unfold LIBB_Tx2Auth.law at source
 rw [dif_pos fits] at source
 let pu := LIB_Bytes.fromBytes pub fits.1
 let proof := LIB_Bytes.fromBytes pr fits.2.1
 let cp := LIB_Bytes.fromBytes ck fits.2.2
 have hpu : NNC_ByteCarriers.host pu.val=pub := LIB_Bytes.bytes_from _ _
 have hpr : NNC_ByteCarriers.host proof.val=pr := LIB_Bytes.bytes_from _ _
 have hcp : NNC_ByteCarriers.host cp.val=ck := LIB_Bytes.bytes_from _ _
 have hp : proof.val.length=57607 := by
  simpa only [←hpr,NNC_ByteCarriers.host,List.length_map,RSL.PROOF_BYTES] using domain.1
 have hc : cp.val.length=1768 := by
  simpa only [←hcp,NNC_ByteCarriers.host,List.length_map,RSL.CHECKPOINT_BYTES] using domain.2.1
 have hu : pu.val.length≤1880 := by
  simpa only [←hpu,NNC_ByteCarriers.host,List.length_map,RSL.STATEMENT_BYTES] using domain.2.2.1
 obtain ⟨records,events,native⟩ := NNT_LawOk.native_of_ok env pu proof cp hp world o source ok
 exact ⟨pu,proof,cp,hpu,hpr,hcp,⟨hp,hc,hu⟩,records,events,native⟩

theorem okHeader (pub pr ck : RSL.Bytes) (env : RSL.Env)
 (o : RSL.Obs (Except V0.VErr Unit))
 (domain : RSL.TX2_241.Dom064 (RSL.TAS.lib V0 (fun _ _ => True) V0.tx2auth) (pub,pr,ck))
 (source : V0.tx2auth pub pr ck env o) (ok : o.exit=.ret (.ok ())) :
 NNH_G1aEnv.header env pub pr ck := by
 obtain ⟨pu,proof,cp,hpu,hpr,hcp,dom,records,events,native⟩ :=
  native_bytes_of_ok env pub pr ck NNH_064Install.frame o domain source ok
 have matched := NNH_064EnvHeader.native env pu proof cp NNH_064Install.frame dom records events native
 unfold NNH_G1aEnv.header
 rw [←hpu,←hpr,←hcp,NNC_ByteCarriers.protocol_host,NNC_ByteCarriers.protocol_host,NNC_ByteCarriers.protocol_host]
 exact matched

def field (S : RSL.TAS.Sig) (I : RSL.TAS.Impl L V0 VL) :
 NNC_G1aL (NNH_G1aEnv.sig S) L V0 VL I where
 w := V0.tx2auth
 lawRefines := lawRefines_weak V0
 writeFree := LIBB_V2Star.writeFree
 okHeader := okHeader
#print axioms native_bytes_of_ok
#print axioms okHeader
#print axioms field
end NNT_G1aLaw
