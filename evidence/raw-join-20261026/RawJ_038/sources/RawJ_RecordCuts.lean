import RawJ_Cuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawJ_RecordCuts
open Aeneas Aeneas.Std Result S2W_NativeConsolidation

def Recorded (f : FirstCut) (s : SecondCut) (saved : alloc.vec.Vec U8) (log : S2W_Trace.Log) : Prop :=
  AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
    f.statement = ok f.semantic ∧
  GExq_RecordTrace.projectLog log =
    [.first f.semantic f.pub f.proof f.split (.Ok saved),.second s.pub s.proof s.checkpoint (.Ok ())]

theorem native (ops : AdapterRw.Ops) (native1 : S2W_ExtractionBoundary.First)
    (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction ops native1 native2 hashv)
    (id : S2W_ExtractionBoundary.Program) (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts)
    (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (saved : alloc.vec.Vec U8)
    (accepted1 : native1 id accounts1 data1 = ok (.Ok saved))
    (accepted2 : native2 id accounts2 data2 slot = ok (.Ok ())) :
    ∃ f s log, SourceCuts ops accounts1 accounts2 saved f s ∧ Recorded f s saved log ∧
      S2W_Trace.run ops (S2W_Observation.two ops id accounts1 data1 accounts2 data2 slot) [] = ok (.Ok saved,log) := by
  obtain ⟨f,s,log,cuts,get,ran,record⟩ := RawJ_Cuts.accepted ops id accounts1 accounts2 data1 data2 slot saved
    ((extraction.stage1 id accounts1 data1).symm.trans accepted1)
    ((extraction.stage2 id accounts2 data2 slot).symm.trans accepted2)
  exact ⟨f,s,log,cuts,⟨get,record⟩,ran⟩

#print axioms native
end AspisR1.RawJ_RecordCuts
end
