import NNH_HostWeak241
import NNH_WeakReaderNative
import NNH_HostPersistence
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_HostNativeCuts
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open NNH_HostCtx NNH_LiteralHost NNH_Libraries S2W_NativeConsolidation
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
 (ref : RSL.TX2_213.Ref L D (RSL.TAS.lib V0 (fun _ _ => True) NNH_064WeakField.w)
  (RSL.TX1_344.asStage1 VL P C)
  (NNE_EntryArgs.args c.j.entry 7 CPH_Program.verifier c.j.data)
  (NNE_Entry.state c.j.entry 0) (envOf c) ⟨.ret (.ok (),post),events⟩)
 (accepted : (S_host L0 copy std).Accepted1 c (model1 c))
 (game : (S_host L0 copy std).Game c (model1 c) (model2 c)) : Nonempty (Packet c) := by
 obtain ⟨p⟩ := NNH_HostWeak241.inputs c _ post events ref
 obtain ⟨s,second,raw,checkpoint,encoded⟩ := NNH_WeakReaderCuts.produce _ _ _ _ _ _ _ _ _ p
 obtain ⟨records,ev,domain,native⟩ := NNH_WeakReaderNative.native _ _ _ _ _ _ _ _ p s second raw checkpoint encoded
 obtain ⟨f,first,root,header⟩ := NNH_HostFirstWriter.writer L0 copy std c accepted
 have cuts := NNH_WeakReaderCuts.join (sdk c) CPH_Program.verifier c.i.entry c.j.entry
  c.j.data (NNH_HostWeak241.clock (envOf c)) c.world.saved f s first second
 have persisted := NNH_HostPersistence.persisted L0 copy std c accepted game f s cuts.1 domain.checkpointExtent
 exact ⟨⟨f,s,cuts.1,cuts.2,root,header,persisted,domain,records,ev,native⟩⟩
#print axioms produce
end AspisR1.NNH_HostNativeCuts
end
