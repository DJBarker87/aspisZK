import S1ValuesOwnedPrepareViewY1V1
import S1AcceptedSemanticNumericV1
set_option autoImplicit false
namespace AspisS1ValuesOwnedInstallation
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller AspisR1CurrentCaller.BorrowedClaimPrepared AspisR1CurrentCaller.InstalledPreparation

/-- Same complete source-model preparation, for every digest carrier/hash.
All original byte/View/semantic/Prepared/scratch witnesses remain present.
Numeric producer ranges are derived, not separately assumed successful. -/
theorem prepare_numeric (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H) (prepared : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (success : verifier.candidate.prepare (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)
      D pub proof hash none input=ok (.Ok prepared,scratch)) :
    ∃ (stored initial semantic : Slice U8) (view : verifier.View) (sem : r1_semantic.Verified H),
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start:=7031#usize,«end»:=7495#usize}=ok stored ∧
      expandValues stored initial=ok (.Ok (),view.y1) ∧
      stored.length=464 ∧ initial.length=928 ∧ view.y1.length=928 ∧
      (∀ j, j<928 → view.y1.val[j]?=
        if j%32<16 then stored.val[(j/32)*16+j%32]? else some 0#u8) ∧
      sourceView proof semantic view.y1=ok (.Ok view) ∧
      (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B).op9 D pub view.semantic hash none=ok (.Ok sem) ∧
      (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B).op8 D sem view hash input=ok (.Ok prepared,scratch) ∧
      AspisS1SemanticArrayRanges.CurrentVerifiedNumeric sem ∧
      ∀ l : Usize, l.val<29 → ∃ parsed : AspisR1CurrentPreparedClaim.Concrete.E,
        AspisR1CurrentPreparedClaim.ClaimParser.field view.y1 l=ok parsed ∧
        AspisR1CurrentPreparedClaim.Concrete.Canonical parsed := by
  obtain ⟨stored,initial,semantic,view,sem,storedCall,expanded,storedLength,
    initialLength,y1Length,bytes,viewCall,semanticCall,newCall,fieldCalls⟩ :=
    prepare_view_y1 ops AspisS1ExtractedRoundChildren.children B D pub proof hash prepared input scratch success
  have verify : S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children
      B D pub view.semantic hash = ok (.Ok sem) := semanticCall
  have numeric := AspisS1SemanticArrayRanges.installed_verify_numeric B D pub view.semantic hash sem verify
  exact ⟨stored,initial,semantic,view,sem,storedCall,expanded,storedLength,
    initialLength,y1Length,bytes,viewCall,semanticCall,newCall,numeric,fieldCalls⟩

#print axioms prepare_numeric
end AspisS1ValuesOwnedInstallation
