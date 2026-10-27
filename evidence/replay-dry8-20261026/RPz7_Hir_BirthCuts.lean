import RPz7_Hir_BirthSuffix
import Hist_ArgumentCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_BirthCuts
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_Schedule Hir_ProvenanceModel
open S2W_NativeConsolidation

theorem source {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) native1 native2 hashv)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (std : S2W_TrustedStd.TrustedStd copy) (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (site : CallAt A) (last : Store) (chosen : Call A)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record)) (final1 final2 : A)
    (accepted1 : first native1 copy allocator (load site.before site.call.layout) id site.call.data site.call.state =
      ok (.Ok (saved,post1,final1)))
    (accepted2 : second native2 allocator (load last chosen.layout) id chosen.data chosen.slot chosen.state =
      ok (.Ok (post2,final2))) :
    ∃ f s v, SourceCuts (DrvC_Installation.sdk c) (load site.before site.call.layout).first
      ((load last chosen.layout).second secondSizes) saved f s ∧
      AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
        f.statement = ok f.semantic ∧
      AdapterRw.r1_pool_adapter.owned.validate_asq8 (DrvC_Installation.sdk c) id
        ((load last chosen.layout).second secondSizes) chosen.data chosen.slot = ok (.Ok v) ∧
      (DrvC_Installation.sdk c).op22 v.statement = ok (.Ok s.encoded) := by
  have n1 := (first_accepted native1 copy std allocator _ id site.call.data site.call.state final1 saved post1 accepted1).1
  have n2 := (second_accepted native2 allocator _ id chosen.data chosen.slot chosen.state final2 post2 accepted2).1
  exact Hist_ArgumentCuts.source (DrvC_Installation.sdk c) id _ _ site.call.data chosen.data chosen.slot saved
    ((extraction.stage1 id _ site.call.data).symm.trans n1)
    ((extraction.stage2 id _ chosen.data chosen.slot).symm.trans n2)

#print axioms source
end AspisR1.Hir_BirthCuts
end
