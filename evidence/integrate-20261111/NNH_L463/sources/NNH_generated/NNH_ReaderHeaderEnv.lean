import NNH_064WeakField
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_ReaderHeaderEnv
open Aeneas Aeneas.Std Result VTop_Stages
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical OraclePortCompactDraft AspisR1Stage2.WireTx2

theorem singleton (env : RSL.Env) (s : Slice U8) (out : Array U8 32#usize)
 (returned : (NJC_ResumeCalls.digest (LIBB_PartitionEnv.digest env)).digest () (singletonParts s)=.ok out) :
 CheckpointBytesDigest.stateOf out=LIBB_HashModel.H env (bytesOf s.val) := by
 have input : NNC_ResumeEvents.parts (singletonParts s)=[LIB_Carriers.bytes s] := rfl
 change Result.ok (LIB_Env.nativeKey (env.sha256 (NNC_ResumeEvents.parts (singletonParts s))))=Result.ok out at returned
 have exactDigest := Result.ok.inj returned
 rw [←exactDigest,input]
 unfold LIBB_HashModel.H
 rw [LIBB_ProtocolBytes.host_native]
 rfl

/-- Header transport needs exactly the two actual singleton calls, with their
original parts. No partition-invariance or total flattened-oracle assumption. -/
theorem calls (env : RSL.Env) (ck proof pub : Slice U8)
 (c : AspisR1Stage2.Tx2ResumeDigests.Calls
  (NJC_ResumeCalls.digest (LIBB_PartitionEnv.digest env)) () ck proof pub)
 (length : ck.val.length=1768) :
 NLW_ReaderHeader.decode (bytesOf ck.val)=
 some (LIBB_HashModel.H env (bytesOf proof.val),LIBB_HashModel.H env (bytesOf pub.val)) := by
 have pf:=AdapterRw.Ranges.selected_exact ck c.storedProof 16#usize 48#usize
  (by decide) (by change 48≤ck.val.length; omega) c.proofField
 have pu:=AdapterRw.Ranges.selected_exact ck c.storedPublic 48#usize 80#usize
  (by decide) (by change 80≤ck.val.length; omega) c.publicField
 have v16 : (16#usize).val=16 := by scalar_tac
 have v48 : (48#usize).val=48 := by scalar_tac
 have v80 : (80#usize).val=80 := by scalar_tac
 have pfBytes : c.storedProof.val=(ck.val.drop 16).take 32 := by
  simpa only [v16,v48,v80] using pf.1
 have puBytes : c.storedPublic.val=(ck.val.drop 48).take 32 := by
  simpa only [v16,v48,v80] using pu.1
 have pp : c.proofParts=singletonParts proof := by
  simpa only [lift,singletonParts,Result.ok.injEq] using c.proofInput.symm
 have up : c.publicParts=singletonParts pub := by
  simpa only [lift,singletonParts,Result.ok.injEq] using c.publicInput.symm
 have proofCall := c.proofCall
 have publicCall := c.publicCall
 rw [pp] at proofCall
 rw [up] at publicCall
 have hp : SemanticRecordCodec.decodeState (slice (bytesOf ck.val) 16 32)=
  some (LIBB_HashModel.H env (bytesOf proof.val)) := by
  rw [←NLW_WriterPair.map_slice,←pfBytes,c.proofEqual,
   ←CheckpointBytesDigest.bytes_stateOf,SemanticRecordCodec.decodeState_bytes,singleton env proof _ proofCall]
 have hu : SemanticRecordCodec.decodeState (slice (bytesOf ck.val) 48 32)=
  some (LIBB_HashModel.H env (bytesOf pub.val)) := by
  rw [←NLW_WriterPair.map_slice,←puBytes,c.publicEqual,
   ←CheckpointBytesDigest.bytes_stateOf,SemanticRecordCodec.decodeState_bytes,singleton env pub _ publicCall]
 simp only [NLW_ReaderHeader.decode,hp,hu,Option.bind_some]
 rfl
#print axioms singleton
#print axioms calls
end AspisR1.NNH_ReaderHeaderEnv
