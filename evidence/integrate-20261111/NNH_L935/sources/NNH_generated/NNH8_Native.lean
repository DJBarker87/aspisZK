import NNH8_Exec
import NNH_Run6Cuts
import NNR_Producers
set_option autoImplicit false
noncomputable section
/-! Run 7 (G0 FINAL): the run-6 native-cut producer chain (NNR_Retime, NNH_HostFirstWriter,
NNH_HostPersistence, NNH_HostWeak241.inputs, NNH_HostNativeCuts.Packet, NNH_Run6Cuts,
NNH_Run6Producers) restated at the corrected host context NOC_HostCtx (seed
NOC_HostSeed.m0 at the environment's reservation bit). Proof bodies are unchanged apart
from the host namespace and the seed; every reused lemma is generic in the seed/sdk. -/
namespace AspisR1.NNH8_Retime
open Aeneas Aeneas.Std Result NOC_HostCtx
open S2W_D189Wrappers
variable {W Tx : Type}
theorem missing (c : Ctx W Tx) : missingLit (NNR_Retime.atSlot c) = missingLit c :=
 NNH8_Exec.clockFree c.sha256 c.fixed.pda (NND_Carrier.reply NND_Carrier.slot c.j.slot)
  c.fixed.clock c.fixed.reservation (NOC_HostSeed.m0 (envOf c).reservation)
theorem sdk_same (c : Ctx W Tx) : sdk (NNR_Retime.atSlot c) = sdk c := by
 change DrvC_Installation.sdk (FIp_Install.configuration c.fixed.indexError
  (IDa_Deployed.deployedConfiguration (missingLit (NNR_Retime.atSlot c)) c.fixed.indexError c.fixed.reservation)
  c.fixed.reservation) = _
 rw [missing c]
theorem first (c : Ctx W Tx) : model1 (NNR_Retime.atSlot c) = model1 c :=
 congrArg AdapterRw.r1_pool_adapter.owned.stage1_owned (sdk_same c)
theorem second (c : Ctx W Tx) : model2 (NNR_Retime.atSlot c) = model2 c :=
 congrArg AdapterRw.r1_pool_adapter.owned.stage2_owned (sdk_same c)
end AspisR1.NNH8_Retime

namespace AspisR1.NNH8_FirstWriter
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_WrapperLaws S2W_D189Consolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open S2W_NativeConsolidation MultiproofConeCanonical S2W_EntryWriteHistory
open NOC_HostCtx
variable {W Tx : Type} (L : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)

theorem owned (c : Ctx W Tx) (accepted : (NOC_Run5bHost.S_host L copy std).Accepted1 c (model1 c)) :
 model1 c CPH_Program.verifier c.i.entry.first c.i.data = .ok (.Ok c.world.saved) := by
 exact (PoolT_Write.accepted_verifier_writes_copy (sdk c) (model1 c) (model2 c) (hashv c)
  (NOC_HostCtx.extraction c) copy std NNE_AbortIndicator.allocator c.i.entry CPH_Program.verifier
  c.i.data true true c.world.saved
  (writeBracket c.i.entry.heap 2 0 0 (source (nativeBytes c.world.saved))) accepted).1

theorem oracle (c : Ctx W Tx) : CheckpointBytes5Inputs.Oracle
 (VTop_Checkpoint.digest (Tx1Q_Install.digest (DrvC_Installation.currentDigest (configuration c)))) () c.sha256 := by
 intro parts digest returned
 change (sdk c).op43 () parts = .ok digest at returned
 rw [(NOC_HostCtx.extraction c).digestSource,S2W_DigestExtraction.digest_eq_hashv] at returned
 exact (DGP_HostDigest.syscall c.sha256).returningValue parts digest returned

theorem writer (c : Ctx W Tx) (accepted : (NOC_Run5bHost.S_host L copy std).Accepted1 c (model1 c)) :
 ∃ f : S2W_NativeConsolidation.FirstCut,
 NNC_FirstCuts.Facts (sdk c) c.i.entry.first c.world.saved f ∧
 NLP_InputDomain.Root0 c.world.saved.deref f.proof ∧
 NLW_ReaderHeader.decode (bytesOf c.world.saved.val) =
  some (c.sha256 (bytesOf f.proof.val),c.sha256 (bytesOf f.pub.val)) := by
 exact NNC_FirstCuts.writer (configuration c) (model1 c) (model2 c) (hashv c)
  (NOC_HostCtx.extraction c) CPH_Program.verifier c.i.entry.first c.i.data c.world.saved
  c.sha256 (oracle c) (owned L copy std c accepted)
end AspisR1.NNH8_FirstWriter

namespace AspisR1.NNH8_Persistence
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical NOC_HostCtx S2W_NativeConsolidation
variable {W Tx : Type} (L : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)

theorem key (c : Ctx W Tx) : (sdk c).op36 = Hist_Authority.keyEq :=
 Rc5_Install.key c.fixed.indexError (FIp_Install.select c.fixed.reservation (base c)) c.fixed.reservation

theorem persisted (c : Ctx W Tx)
 (accepted : (NOC_Run5bHost.S_host L copy std).Accepted1 c (model1 c))
 (game : (NOC_Run5bHost.S_host L copy std).Game c (model1 c) (model2 c))
 (f : FirstCut) (s : SecondCut)
 (cuts : NNC_SourceCuts.Cuts (sdk c) c.i.entry.first
  (c.j.entry.second secondSizes) c.world.saved f s)
 (length : s.checkpoint.val.length = 1768) :
 bytesOf s.checkpoint.val = bytesOf c.world.saved.val := by
 exact NNC_NativePersistence.persisted c.world.p c.world.t c.world.u (configuration c) (key c)
  c.i.entry c.j.entry c.world.saved c.world.actions (model1 c) (model2 c) (hashv c)
  (NOC_HostCtx.extraction c) copy std NNE_AbortIndicator.allocator CPH_Program.verifier
  (Hist_Nonvacuity.key 0#u8) CPH_Program.not_system game.1 game.2.2.2
  c.i.data true true (NNH_HostExec.post c.i c.world.saved) accepted f s cuts length
end AspisR1.NNH8_Persistence

namespace AspisR1.NNH8_Weak241
open Aeneas Aeneas.Std Result NOC_HostCtx NNH_Libraries
open S2W_D189Wrappers
theorem inputs {W Tx : Type} (c : Ctx W Tx) (V : RSL.TX2_241.V2Lib)
 (post : RSL.SdkState) (events : List RSL.Event)
 (ref : RSL.TX2_213.Ref L D V (RSL.TX1_344.asStage1 VL P C)
  (NNE_EntryArgs.args c.j.entry 7 CPH_Program.verifier c.j.data)
  (NNE_Entry.state c.j.entry 0) (envOf c) ⟨.ret (.ok (),post),events⟩) :
 Nonempty (NNH_WeakTx2Inputs.Packet (NOC_HostSeed.m0 (envOf c).reservation) (envOf c) c.fixed.indexError
  c.fixed.reservation V CPH_Program.verifier (c.j.entry.second secondSizes) c.j.data
  (NNH_HostWeak241.clock (envOf c))) := by
 obtain ⟨es,child⟩ := NNH_HostWeak241.reference c V post events ref
 apply NNH_WeakTx2Inputs.produce _ _ _ _ V CPH_Program.verifier _ c.j.data (NNH_HostWeak241.clock (envOf c)) es
 simpa only [NNH_HostWeak241.clock_reply] using child
end AspisR1.NNH8_Weak241

namespace AspisR1.NNH8_NativeCuts
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open NOC_HostCtx NNH_Libraries S2W_NativeConsolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical
variable {W Tx : Type} (L0 : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)
structure Packet (c : Ctx W Tx) where
 f : FirstCut
 s : SecondCut
 cuts : NNC_SourceCuts.Cuts (sdk c) c.i.entry.first (c.j.entry.second secondSizes) c.world.saved f s
 origin : P2P_Origin.Fact (sdk c) CPH_Program.verifier (c.j.entry.second secondSizes)
  c.j.data (NNH_HostWeak241.clock (envOf c)) s
 writerRoot : NLP_InputDomain.Root0 c.world.saved.deref f.proof
 writerHeader : NLW_ReaderHeader.decode (bytesOf c.world.saved.val) =
  some (c.sha256 (bytesOf f.proof.val),c.sha256 (bytesOf f.pub.val))
 persisted : bytesOf s.checkpoint.val = bytesOf c.world.saved.val
 domain : NNC_064Weak.Domain (NLW_Full064.Args.mk (LIBB_PartitionEnv.digest (envOf c)) s.pub s.proof s.checkpoint ())
 records : List (NLT_NativeInvocation.Occurrence (LIBB_PartitionEnv.H (envOf c)) (LIBB_PartitionEnv.digest (envOf c)) ())
 events : List (NLW_Full064.Event Unit Unit)
 native : NMN_064.Native (LIBB_PartitionEnv.H (envOf c))
  ⟨⟨LIBB_PartitionEnv.digest (envOf c),s.pub,s.proof,s.checkpoint,()⟩,NNH_064Install.frame⟩
  (.common (.resolved (.ok (.Ok ())) records)) events

theorem produce (c : Ctx W Tx) (post : RSL.SdkState) (events : List RSL.Event)
 (ref : RSL.TX2_213.Ref L D (RSL.TAS.lib V0 (fun _ _ => True) V0.tx2auth)
  (RSL.TX1_344.asStage1 VL P C)
  (NNE_EntryArgs.args c.j.entry 7 CPH_Program.verifier c.j.data)
  (NNE_Entry.state c.j.entry 0) (envOf c) ⟨.ret (.ok (),post),events⟩)
 (accepted : (NOC_Run5bHost.S_host L0 copy std).Accepted1 c (model1 c))
 (game : (NOC_Run5bHost.S_host L0 copy std).Game c (model1 c) (model2 c)) : Nonempty (Packet c) := by
 obtain ⟨p⟩ := NNH8_Weak241.inputs c _ post events ref
 obtain ⟨s,second,raw,checkpoint,encoded⟩ := NNH_WeakReaderCuts.produce _ _ _ _ _ _ _ _ _ p
 obtain ⟨records,ev,domain,native⟩ := NNH_Run6ReaderNative.native _ _ _ _ _ _ _ _ p s second raw checkpoint encoded
 obtain ⟨f,first,root,header⟩ := NNH8_FirstWriter.writer L0 copy std c accepted
 have cuts := NNH_WeakReaderCuts.join (sdk c) CPH_Program.verifier c.i.entry c.j.entry
  c.j.data (NNH_HostWeak241.clock (envOf c)) c.world.saved f s first second
 have persisted := NNH8_Persistence.persisted L0 copy std c accepted game f s cuts.1 domain.checkpointExtent
 exact ⟨⟨f,s,cuts.1,cuts.2,root,header,persisted,domain,records,ev,native⟩⟩
end AspisR1.NNH8_NativeCuts

namespace AspisR1.NNH8_Producers
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open NOC_HostCtx NNH_Libraries S2W_NativeConsolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep MultiproofConeCanonical
variable {W Tx : Type} (L0 : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)

theorem accepted (c : Ctx W Tx) :
 (NOC_Run5bHost.S_host L0 copy std).Accepted1 (NNR_Retime.atSlot c) (model1 (NNR_Retime.atSlot c)) ↔
 (NOC_Run5bHost.S_host L0 copy std).Accepted1 c (model1 c) := by
 change S2W_D189Wrappers.first (model1 (NNR_Retime.atSlot c)) copy NNE_AbortIndicator.allocator
  c.i.entry CPH_Program.verifier c.i.data true = _ ↔ _
 rw [NNH8_Retime.first]
 rfl

theorem game (c : Ctx W Tx) :
 (NOC_Run5bHost.S_host L0 copy std).Game (NNR_Retime.atSlot c) (model1 (NNR_Retime.atSlot c)) (model2 (NNR_Retime.atSlot c)) ↔
 (NOC_Run5bHost.S_host L0 copy std).Game c (model1 c) (model2 c) := by
 change (CPH_Game.DeployedPairExecution c.world.p c.world.t c.world.u c.i.entry c.j.entry
  c.world.saved c.world.actions (model1 (NNR_Retime.atSlot c)) (model2 (NNR_Retime.atSlot c))
  copy NNE_AbortIndicator.allocator CPH_Program.verifier ∧ NOC_Run5bHost.retained L0 c) ↔ _
 rw [NNH8_Retime.first,NNH8_Retime.second]
 rfl

theorem produce (c : Ctx W Tx) (post : RSL.SdkState) (events : List RSL.Event)
 (ref : RSL.TX2_213.Ref L D (RSL.TAS.lib V0 (fun _ _ => True) V0.tx2auth)
  (RSL.TX1_344.asStage1 VL P C)
  (NNE_EntryArgs.args c.j.entry 7 CPH_Program.verifier c.j.data)
  (NNE_Entry.state c.j.entry 0) (NFB_NMFBHost.env2 c) ⟨.ret (.ok (),post),events⟩)
 (acc : (NOC_Run5bHost.S_host L0 copy std).Accepted1 c (model1 c))
 (run : (NOC_Run5bHost.S_host L0 copy std).Game c (model1 c) (model2 c)) :
 Nonempty (NNH8_NativeCuts.Packet (NNR_Retime.atSlot c)) :=
 NNH8_NativeCuts.produce L0 copy std (NNR_Retime.atSlot c) post events ref
  ((accepted L0 copy std c).mpr acc) ((game L0 copy std c).mpr run)

theorem origin (c : Ctx W Tx) (p : NNH8_NativeCuts.Packet (NNR_Retime.atSlot c)) :
 P2P_Origin.Fact (sdk c) CPH_Program.verifier (c.j.entry.second secondSizes) c.j.data c.j.slot p.s := by
 have h := p.origin
 have e : NNH_HostWeak241.clock (envOf (NNR_Retime.atSlot c)) = c.j.slot := NNR_Clock.M1a c
 rw [NNH8_Retime.sdk_same,e] at h
 exact h
end AspisR1.NNH8_Producers
end
#print axioms AspisR1.NNH8_Retime.missing
#print axioms AspisR1.NNH8_Retime.sdk_same
#print axioms AspisR1.NNH8_FirstWriter.writer
#print axioms AspisR1.NNH8_Persistence.persisted
#print axioms AspisR1.NNH8_Weak241.inputs
#print axioms AspisR1.NNH8_NativeCuts.produce
#print axioms AspisR1.NNH8_Producers.produce
#print axioms AspisR1.NNH8_Producers.origin
