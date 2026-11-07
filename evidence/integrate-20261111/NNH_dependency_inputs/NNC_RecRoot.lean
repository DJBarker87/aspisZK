import NNC_RecBinding
set_option autoImplicit false
noncomputable section
namespace NNC_RecRoot
open Aeneas Aeneas.Std Result AspisR1 MultiproofConeCanonical S2W_NativeConsolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw FS FS2
/-- Native weak064 fold with the adversary-output selector. No TX2 model
Result/Calls or Root0 premise. SAME occurrence production is still the caller's
full weak row fold; this theorem does not invent that association. -/
theorem root0_or_rec_collision {A Ambient X : Type}
 (source : Program Bytes State A)
 (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
 (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
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
  (.common (.resolved (ok (.Ok ())) records)) events)
 (selects : select (eval H source).2 = P2P_NativeSelection.pair ops id e1 e2 data2 slot) :
 (NLP_InputDomain.Root0 s.checkpoint s.proof ∧
  NLT_CompleteRoot.RowSpec H d s.pub s.proof s.checkpoint hash) ∨
 BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
  (eval H (Hiq_RecordedJoint.program source project
   select)) := by
 have readerHeader := NNC_064Weak.accepted_header H
  ⟨⟨d,s.pub,s.proof,s.checkpoint,hash⟩,world⟩ domain oracle records events native
 have alternative := NNC_RecBinding.from_headers source project select Q budget H ops id
  e1 e2 data2 slot saved f s cuts origin writerRoot persisted writerHeader selects readerHeader
 rcases alternative with root0 | bad
 · exact Or.inl ⟨root0,NLT_CompleteRoot.root H d s.pub s.proof s.checkpoint hash
    domain.proofExtent domain.publicBound root0⟩
 · exact Or.inr bad

#print axioms root0_or_rec_collision
end NNC_RecRoot
