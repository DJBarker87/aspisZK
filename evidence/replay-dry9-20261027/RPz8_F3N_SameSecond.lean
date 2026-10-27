import RPz7_F3N_ConsDictionary
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_SameSecond
open Aeneas Aeneas.Std Result S2W_NativeConsolidation

theorem from_cut {F C : Type} (a : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (SdkD_PairBatches.dictionary a ops stage finish reserved query geo B std)
      accounts1 accounts2 saved f s) :
    ∃ tx2 : Cons_Native.Witness,
      Cons_Native.Calls (AuS1_Install.base stage) finish reserved query geo
        (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
          (SdkD_PairBatches.dictionary a ops stage finish reserved query geo B std)) ()
        s.pub s.proof s.checkpoint tx2 ∧
      Cons_NativeBuild.Aux reserved query geo
        (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
          (SdkD_PairBatches.dictionary a ops stage finish reserved query geo B std)) ()
        s.pub s.proof s.checkpoint tx2 := by
  have source := Cons_Second.accepted a ops stage finish reserved query geo B std accounts1 accounts2 saved f s
    (by rw [← AuS1_Install.dictionary];exact cuts)
  simpa only [← AuS1_Install.dictionary] using source

#print axioms from_cut
end AspisR1.F3N_SameSecond
end
