import NNC_064Weak
import NNC_SourceCuts
set_option autoImplicit false
noncomputable section
namespace NNC_BindingRoot
open Aeneas Aeneas.Std Result AspisR1 MultiproofConeCanonical S2W_NativeConsolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw FS FS2
/-- Header comparisons alone produce the existing digestMatches premise.
The binding branch then transports Root0 by BYTE equality, not injectivity. -/
theorem root0_of_binding (H : Bytes → State) (saved : alloc.vec.Vec U8)
 (f : FirstCut) (s : SecondCut)
 (writerRoot : NLP_InputDomain.Root0 saved.deref f.proof)
 (persisted : bytesOf s.checkpoint.val=bytesOf saved.val)
 (writerHeader : NLW_ReaderHeader.decode (bytesOf saved.val)=
  some (H (bytesOf f.proof.val),H (bytesOf f.pub.val)))
 (readerHeader : NLW_ReaderHeader.decode (bytesOf s.checkpoint.val)=
  some (H (bytesOf s.proof.val),H (bytesOf s.pub.val)))
 (binding : R9PoolRuntimeBinding.P2Prime H
  ⟨bytesOf f.proof.val,bytesOf f.pub.val⟩ ⟨bytesOf s.proof.val,bytesOf s.pub.val⟩) :
 NLP_InputDomain.Root0 s.checkpoint s.proof := by
 have matched:=NLW_AuthenticatedRoots.digest_matches H saved.deref s.checkpoint
  f.proof f.pub s.proof s.pub persisted writerHeader readerHeader
 exact NMF_InputTransport.root0 saved.deref s.checkpoint f.proof s.proof writerRoot persisted
  (binding matched).1
/-- NMF' core fold. Its native premises are SAME-occurrence read/range cuts,
writer facts, persistence and an entered native064 outcome; none is a TX2
model Result/Calls or Root0 assumption. NMS/physical adapters own production
of the cuts/persistence from their full row packets. The charged event is
literally the existing source/project/selector with Q+2965, with no new loss. -/
theorem root0_or_existing_collision {A Ambient X : Type}
 (source : Program Bytes State A)
 (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
 (Q : Nat) (budget : ∀ H,firstReads emptyTable (eval H source).1≤Q+1921)
 (H : Bytes → State) (ops : AdapterRw.Ops) (id : S2W_ExtractionBoundary.Program)
 (e1 e2 : S2W_D189Entry.Entry) (data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
 (saved : alloc.vec.Vec U8) (f : FirstCut) (s : SecondCut)
 (cuts : NNC_SourceCuts.Cuts ops e1.first (e2.second S2W_D189Wrappers.secondSizes) saved f s)
 (origin : P2P_Origin.Fact ops id (e2.second S2W_D189Wrappers.secondSizes) data2 slot s)
 (writerRoot : NLP_InputDomain.Root0 saved.deref f.proof)
 (persisted : bytesOf s.checkpoint.val=bytesOf saved.val)
 (writerHeader : NLW_ReaderHeader.decode (bytesOf saved.val)=
  some (H (bytesOf f.proof.val),H (bytesOf f.pub.val)))
 (d : VTop_Stages.aspis_core.digest.Digest32 X) (hash : X)
 (world : NLM_PacketTypes.World Ambient)
 (domain : NNC_064Weak.Domain (NLW_Full064.Args.mk d s.pub s.proof s.checkpoint hash))
 (oracle : CheckpointBytes5Inputs.Oracle (VTop_Checkpoint.digest d) hash H)
 (records : List (NLT_NativeInvocation.Occurrence H d hash))
 (events : List (NLW_Full064.Event Ambient X))
 (native : NMN_064.Native H ⟨⟨d,s.pub,s.proof,s.checkpoint,hash⟩,world⟩
  (.common (.resolved (ok (.Ok ())) records)) events) :
 (NLP_InputDomain.Root0 s.checkpoint s.proof ∧
  NLT_CompleteRoot.RowSpec H d s.pub s.proof s.checkpoint hash) ∨
 BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
  (eval H (Hiq_RecordedJoint.program source project
   (fun _=>P2P_NativeSelection.pair ops id e1 e2 data2 slot))) := by
 have alternative:=P2P_Charge.binding_or_collision source project
  (fun _=>P2P_NativeSelection.pair ops id e1 e2 data2 slot) Q budget H
 rcases alternative with bad | good
 · exact Or.inr bad
 · have association:=NNC_SourceCuts.on_cuts ops id e1 e2 data2 slot saved f s cuts origin
   change R9PoolRuntimeBinding.P2Prime H
    (P2P_NativeSelection.pair ops id e1 e2 data2 slot).1
    (P2P_NativeSelection.pair ops id e1 e2 data2 slot).2 at good
   rw [association] at good
   have readerHeader:=NNC_064Weak.accepted_header H
    ⟨⟨d,s.pub,s.proof,s.checkpoint,hash⟩,world⟩ domain oracle records events native
   have root0:=root0_of_binding H saved f s writerRoot persisted writerHeader readerHeader good
   exact Or.inl ⟨root0,NLT_CompleteRoot.root H d s.pub s.proof s.checkpoint hash
    domain.proofExtent domain.publicBound root0⟩
/-- The row consumer is evaluated only in the Root0 arm. The event arm is
returned directly, independent of any TX2 row behavior or model run. -/
theorem case_split {Row Event Conclusion : Prop}
 (alternative : Row ∨ Event) (rootBranch : Row → Conclusion) : Conclusion ∨ Event := by
 rcases alternative with row | event
 · exact Or.inl (rootBranch row)
 · exact Or.inr event
#print root0_or_existing_collision
#print axioms root0_of_binding
#print axioms root0_or_existing_collision
#print axioms case_split
end NNC_BindingRoot
