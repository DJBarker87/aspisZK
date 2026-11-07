import NNH_064EnvHeader
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_G1aEnv
open Aeneas Aeneas.Std VTop_Stages NNH_Libraries NNH_064Install NNH_064WeakField

def header (env : RSL.Env) (pub pr ck : RSL.Bytes) : Prop :=
 NLW_ReaderHeader.decode (NNC_ByteCarriers.protocol ck)=
 some (LIBB_HashModel.H env (NNC_ByteCarriers.protocol pr),
       LIBB_HashModel.H env (NNC_ByteCarriers.protocol pub))

theorem okHeader (pub pr ck : RSL.Bytes) (env : RSL.Env)
 (o : RSL.Obs (Except V0.VErr Unit))
 (domain : RSL.TX2_241.Dom064 (RSL.TAS.lib V0 (fun _ _=>True) w) (pub,pr,ck))
 (source : w pub pr ck env o) (ok : o.exit=.ret (.ok ())) : header env pub pr ck := by
 obtain ⟨pu,proof,cp,hpu,hpr,hcp,outcome,events,trace,native,traceSource,equal⟩ := source
 have returned : NNC_WeakSpec.exit (LIBB_PartitionEnv.H env) _ outcome=.ret (.ok ()) :=
  (congrArg RSL.Obs.exit equal).symm.trans ok
 obtain ⟨records,rfl⟩ := NNC_WeakSpec.exit_ok (LIBB_PartitionEnv.H env) _ outcome returned
 have hp : proof.val.length=57607 := by
  simpa only [←hpr,NNC_ByteCarriers.host,List.length_map,RSL.PROOF_BYTES] using domain.1
 have hc : cp.val.length=1768 := by
  simpa only [←hcp,NNC_ByteCarriers.host,List.length_map,RSL.CHECKPOINT_BYTES] using domain.2.1
 have hu : pu.val.length ≤ 1880 := by
  simpa only [←hpu,NNC_ByteCarriers.host,List.length_map,RSL.STATEMENT_BYTES] using domain.2.2.1
 have matched := NNH_064EnvHeader.native env pu proof cp NNH_064Install.frame ⟨hp,hc,hu⟩ records events native
 unfold header
 rw [←hpu,←hpr,←hcp,NNC_ByteCarriers.protocol_host,NNC_ByteCarriers.protocol_host,NNC_ByteCarriers.protocol_host]
 exact matched

def sig (S : RSL.TAS.Sig) : RSL.TAS.Sig := {S with readerHeader:=header}

/-- Every G1a proof field is instantiated by the SAME computed064 observer.
The selected physical recorder/Root0-or-E_rec inclusion is a separate field. -/
def field (S : RSL.TAS.Sig) (I0 : RSL.TAS.Impl L V0 VL) :
 RSL.TAS.NNC_G1a (sig S) L V0 VL (NNH_064Install.install I0) where
 w := w
 weak := weak
 writeFree := writeFree
 okHeader := okHeader
#print axioms okHeader
#print axioms field
end AspisR1.NNH_G1aEnv
