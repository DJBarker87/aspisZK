import NNC_BindingRoot
import TAS_Interfaces
set_option autoImplicit false
noncomputable section
namespace NNC_RecBinding
open Aeneas Aeneas.Std AspisR1 MultiproofConeCanonical S2W_NativeConsolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw FS FS2 RSL.TAS
/-- After G1a supplies the matched reader header, this alternative mentions
NO TX2 native behavior, accepted2, common row law, or reader Root0 premise. -/
theorem from_headers {A : Type} (source : Program Bytes State A)
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
 (selects : select (eval H source).2 = P2P_NativeSelection.pair ops id e1 e2 data2 slot)
 (readerHeader : NLW_ReaderHeader.decode (bytesOf s.checkpoint.val)=
  some (H (bytesOf s.proof.val),H (bytesOf s.pub.val))) :
 NLP_InputDomain.Root0 s.checkpoint s.proof ∨
 BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
  (eval H (Hiq_RecordedJoint.program source project
   select)) := by
 rcases P2P_Charge.binding_or_collision source project
  select Q budget H with bad | good
 · exact Or.inr bad
 · have association := NNC_SourceCuts.on_cuts ops id e1 e2 data2 slot saved f s cuts origin
   rw [selects] at good
   change R9PoolRuntimeBinding.P2Prime H
    (P2P_NativeSelection.pair ops id e1 e2 data2 slot).1
    (P2P_NativeSelection.pair ops id e1 e2 data2 slot).2 at good
   rw [association] at good
   exact Or.inl (NNC_BindingRoot.root0_of_binding H saved f s writerRoot persisted writerHeader readerHeader good)


#print axioms from_headers
end NNC_RecBinding
