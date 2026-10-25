import F3_Model
import RawJ_RecordCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3_NativeCarriers
open Aeneas Aeneas.Std Result
open S2W_NativeConsolidation MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def first (f : FirstCut) : F3_Model.PhysicalPublic := ⟨bytesOf f.pub.val⟩
def second (s : SecondCut) : F3_Model.PhysicalPublic := ⟨bytesOf s.pub.val⟩

/-- Physical public bytes come from the original decoded ASF8 account and
reconstructed TX2 array on the SAME native pair. Semantic selection stays a
separate source fact. No full-verifier join is claimed by this theorem. -/
theorem native (ops : AdapterRw.Ops) (native1 : S2W_ExtractionBoundary.First)
    (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction ops native1 native2 hashv)
    (id : S2W_ExtractionBoundary.Program) (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts)
    (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (saved : alloc.vec.Vec U8)
    (accepted1 : native1 id accounts1 data1 = ok (.Ok saved))
    (accepted2 : native2 id accounts2 data2 slot = ok (.Ok ())) :
    ∃ f s log,
      SourceCuts ops accounts1 accounts2 saved f s ∧
      RawJ_RecordCuts.Recorded f s saved log ∧
      S2W_Trace.run ops (S2W_Observation.two ops id accounts1 data1 accounts2 data2 slot) [] =
        ok (.Ok saved,log) ∧
      ops.op47 f.pub = ok (.Ok f.statement) ∧
      AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
        f.statement = ok f.semantic ∧
      (first f).bytes = bytesOf f.pub.val ∧
      (second s).bytes = bytesOf (Array.to_slice s.encoded).val := by
  obtain ⟨f,s,log,cuts,recorded,ran⟩ := RawJ_RecordCuts.native ops native1 native2 hashv extraction
    id accounts1 accounts2 data1 data2 slot saved accepted1 accepted2
  exact ⟨f,s,log,cuts,recorded,ran,cuts.decode,recorded.1,rfl,rfl⟩

/-- Equality of P at checkpoint writer and reader uses the existing, named
child/header, protected-history and P2-prime boundaries. Acceptance alone
has not discharged these boundaries. No equality P=U is required. -/
theorem authenticated (ops : AdapterRw.Ops) (H : Bytes → State)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : FirstCut) (s : SecondCut) (cuts : SourceCuts ops accounts1 accounts2 saved f s)
    (decode : S2W_AuthenticatedInputs.HeaderDecode)
    (writer : S2W_AuthenticatedInputs.CheckpointWriterConeJoin ops decode H f.semantic f.pub f.proof f.split)
    (reader : S2W_AuthenticatedInputs.CheckpointReaderConeJoin ops decode H s.pub s.proof s.checkpoint)
    (version : S2W_AuthenticatedInputs.CheckpointVersionBinding (bytesOf saved.val) (bytesOf s.checkpoint.val))
    (p2prime : S2W_AuthenticatedInputs.P2Prime H f.proof f.pub s.proof s.pub) :
    second s = first f ∧ bytesOf s.proof.val = bytesOf f.proof.val ∧
      bytesOf s.checkpoint.val = bytesOf saved.val ∧ (bytesOf saved.val).length = 1768 := by
  obtain ⟨proof,pub,ck,size⟩ := S2W_AuthenticatedInputs.authenticated_inputs ops decode H
    f.semantic f.pub f.proof s.pub s.proof s.checkpoint f.split saved
    cuts.first cuts.second writer reader version p2prime
  exact ⟨congrArg F3_Model.PhysicalPublic.mk pub,proof,ck,size⟩

#print axioms native
#print axioms authenticated
end AspisR1.F3_NativeCarriers
end
