import Hir_SelectedVersion
import Hiq_Association
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_SelectAssociation
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_Schedule Hir_ProvenanceModel Hir_WriterSelect Hir_LifetimeExperiment
open S2W_NativeConsolidation

theorem source {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (native1 : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (execution : Execution A) (writer : Writer A) (last : Store) (chosen : Call A)
    (reply : GExq_AccountExperiment.SecondReply A)
    (selected : pairOf native1 copy allocator id execution =
      some (Hir_FirstChoice.input writer.site.before writer.site.call,.ok (.Ok (writer.saved,writer.post,writer.final)),
        some (Hir_Choice.input last chosen,reply)))
    (f : FirstCut) (s : SecondCut) (v : AdapterRw.r1_pool_adapter.ValidatedAsqa)
    (cuts : SourceCuts (DrvC_Installation.sdk c) (load writer.site.before writer.site.call.layout).first
      ((load last chosen.layout).second secondSizes) writer.saved f s)
    (validation : AdapterRw.r1_pool_adapter.owned.validate_asq8 (DrvC_Installation.sdk c) id
      ((load last chosen.layout).second secondSizes) chosen.data chosen.slot = ok (.Ok v))
    (encoding : (DrvC_Installation.sdk c).op22 v.statement = ok (.Ok s.encoded)) :
    select c native1 copy allocator id execution = Hist_PairExperiment.select ⟨f,s⟩ := by
  simp only [select,selected]
  exact Hiq_Association.selected (DrvC_Installation.sdk c) id
    (Hir_FirstChoice.input writer.site.before writer.site.call) (Hir_Choice.input last chosen)
    (.ok (.Ok (writer.saved,writer.post,writer.final))) reply writer.saved f s v cuts validation encoding

#print axioms source
end AspisR1.Hir_SelectAssociation
end
