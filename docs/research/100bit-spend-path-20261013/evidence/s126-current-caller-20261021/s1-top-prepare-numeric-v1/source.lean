import S1TopPrepareY1ProvenanceV1
import S1AcceptedSemanticNumericV1
set_option autoImplicit false
noncomputable section
namespace AspisS1TopPrepareCode
open Aeneas Aeneas.Std Result
open AspisS1TopPrepareCarrier AspisR1ClaimPreparedBridge
open AspisR1PublicPreparation.PreparedHashCode
open AspisR1CurrentCaller.BorrowedClaimPrepared
open AspisS1ValuesOwnedInstallation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw
open S4SolanaDigestWrapperP3BindingV1

/-- Original complete Y1 witness with numeric ranges added on its SAME sem. -/
def NumericY1Provenance (base : AspisR1CurrentCaller.Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash)
    (pub : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : Hash) (input scratch : Array Top.E 29#usize) (prepared : Top.Prepared) : Prop :=
  ∃ (current : Current.Prepared) (g : Array Current.E 29#usize)
    (stored initial semantic : Slice U8) (view : AspisR1CurrentCaller.verifier.View)
    (sem : AspisR1CurrentCaller.r1_semantic.Verified Hash),
    prepared=toPrepared current ∧ scratch=mapArray toE g ∧
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proof {start:=7031#usize,«end»:=7495#usize}=ok stored ∧
    expandValues stored initial=ok (.Ok (),view.y1) ∧
    stored.length=464 ∧ initial.length=928 ∧ view.y1.length=928 ∧
    (∀ j, j<928 → view.y1.val[j]?=
      if j%32<16 then stored.val[(j/32)*16+j%32]? else some 0#u8) ∧
    AspisR1CurrentCaller.InstalledPreparation.sourceView proof semantic view.y1=ok (.Ok view) ∧
    (NativeBuffers.install (withValues base) nativeValues AspisS1ExtractedRoundChildren.children B).op9
      (AspisS1TopPrepareSource.currentDigest D) (AspisS6CurrentVerifierCarrier.toPublic pub)
      view.semantic hash none=ok (.Ok sem) ∧
    (NativeBuffers.install (withValues base) nativeValues AspisS1ExtractedRoundChildren.children B).op8
      (AspisS1TopPrepareSource.currentDigest D) sem view hash (mapArray fromE input)=ok (.Ok current,g) ∧
    AspisS1AcceptedRoundsNumeric.CurrentVerifiedNumeric sem ∧
    ∀ l : Usize, l.val<29 → ∃ parsed : AspisR1CurrentPreparedClaim.Concrete.E,
      AspisR1CurrentPreparedClaim.ClaimParser.field view.y1 l=ok parsed ∧
      AspisR1CurrentPreparedClaim.Concrete.Canonical parsed

/-- Same complete preparation return; the actual semantic producer supplies
all numeric ranges. No extra successful decode/sample/update is a premise. -/
theorem source_numeric_y1 (base : AspisR1CurrentCaller.Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash)
    (pub : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : Hash) (input scratch : Array Top.E 29#usize) (prepared : Top.Prepared)
    (accepted : AspisS1TopPrepareSource.prepare (sourceOps base AspisS1ExtractedRoundChildren.children B)
      D pub proof hash none input=ok (.Ok prepared,scratch)) :
    NumericY1Provenance base B D pub proof hash input scratch prepared := by
  obtain ⟨current,g,stored,initial,semantic,view,sem,same,scratchEq,storedRange,codec,
    storedLength,initialLength,y1Length,bytes,viewCall,semanticCall,newCall,fieldCalls⟩ :=
    source_y1_provenance base AspisS1ExtractedRoundChildren.children B D pub proof hash input scratch prepared accepted
  have verify : AspisR1CurrentCaller.S1SemanticInstallation.verify
      AspisS1ExtractedRoundChildren.children B (AspisS1TopPrepareSource.currentDigest D)
      (AspisS6CurrentVerifierCarrier.toPublic pub) view.semantic hash = ok (.Ok sem) := semanticCall
  have numeric := AspisS1AcceptedRoundsNumeric.installed_verify_numeric B _ _ _ _ sem verify
  exact ⟨current,g,stored,initial,semantic,view,sem,same,scratchEq,storedRange,codec,
    storedLength,initialLength,y1Length,bytes,viewCall,semanticCall,newCall,numeric,fieldCalls⟩

/-- Actual complete installed release op7, all H replies, same source effects
and read bound. Only the accepted parent is a dynamic success premise. -/
theorem installed_numeric_y1 (base : AspisR1CurrentCaller.Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (other : AspisR1.VTop_OracleCode.Implementation) (H : Bytes → State)
    (pub : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : SolanaDigest) (input scratch : Array Top.E 29#usize) (prepared : Top.Prepared)
    (accepted : (eval H (body base AspisS1ExtractedRoundChildren.children B other
      (.op7 (digest (fun bytes => encodeState (H bytes))) pub proof hash none input))).2=
        ok (.Ok prepared,scratch)) :
    (eval H (body base AspisS1ExtractedRoundChildren.children B other
      (.op7 (digest (fun bytes => encodeState (H bytes))) pub proof hash none input))).1.length ≤ 115 ∧
    NumericY1Provenance base B (digest (fun bytes => encodeState (H bytes))) pub proof hash input scratch prepared := by
  have effects := installed_effects_count base AspisS1ExtractedRoundChildren.children B other H pub proof hash input
  have source : AspisS1TopPrepareSource.prepare (sourceOps base AspisS1ExtractedRoundChildren.children B)
      (digest (fun bytes => encodeState (H bytes))) pub proof hash none input=ok (.Ok prepared,scratch) := by
    rw [effects.1] at accepted
    exact accepted
  exact ⟨effects.2,source_numeric_y1 base B _ pub proof hash input scratch prepared source⟩

#print NumericY1Provenance
#print axioms source_numeric_y1
#print axioms installed_numeric_y1
end AspisS1TopPrepareCode
