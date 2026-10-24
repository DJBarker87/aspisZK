import S1ValuesOwnedPrepareViewY1V1
import S1TopPrepareBudgetV1
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

/-- Complete same-call witnesses. View.y1 itself, rather than an unrelated
expanded buffer witness, has the exact stored input and expanded bytes. -/
def Y1Provenance (base : AspisR1CurrentCaller.Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
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
    (NativeBuffers.install (withValues base) nativeValues R B).op9
      (AspisS1TopPrepareSource.currentDigest D) (AspisS6CurrentVerifierCarrier.toPublic pub)
      view.semantic hash none=ok (.Ok sem) ∧
    (NativeBuffers.install (withValues base) nativeValues R B).op8
      (AspisS1TopPrepareSource.currentDigest D) sem view hash (mapArray fromE input)=ok (.Ok current,g) ∧
    ∀ l : Usize, l.val<29 → ∃ parsed : AspisR1CurrentPreparedClaim.Concrete.E,
      AspisR1CurrentPreparedClaim.ClaimParser.field view.y1 l=ok parsed ∧
      AspisR1CurrentPreparedClaim.Concrete.Canonical parsed

/-- No separately chosen View, codec success, length or buffer equality. -/
theorem source_y1_provenance (base : AspisR1CurrentCaller.Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash)
    (pub : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : Hash) (input scratch : Array Top.E 29#usize) (prepared : Top.Prepared)
    (accepted : AspisS1TopPrepareSource.prepare (sourceOps base R B) D pub proof hash none input=
      ok (.Ok prepared,scratch)) :
    Y1Provenance base R B D pub proof hash input scratch prepared := by
  obtain ⟨current,g,source,same,scratchEq⟩ :=
    AspisS1TopPrepareSource.prepare_return (sourceOps base R B) D pub proof hash input scratch prepared accepted
  obtain ⟨stored,initial,semantic,view,sem,storedRange,codec,storedLength,initialLength,y1Length,
    bytes,viewCall,semanticCall,newCall,fieldCalls⟩ :=
    prepare_view_y1 base R B (AspisS1TopPrepareSource.currentDigest D)
      (AspisS6CurrentVerifierCarrier.toPublic pub) proof hash current (mapArray fromE input) g source
  exact ⟨current,g,stored,initial,semantic,view,sem,same,scratchEq,storedRange,codec,
    storedLength,initialLength,y1Length,bytes,viewCall,semanticCall,newCall,fieldCalls⟩

/-- At the actual complete installed release op7 call, derive Y1 provenance
and the read bound from the SAME accepted evaluation, with all H replies.
Native SDK/primitive and release identification remain outside this result. -/
theorem installed_y1_provenance (base : AspisR1CurrentCaller.Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (other : AspisR1.VTop_OracleCode.Implementation) (H : Bytes → State)
    (pub : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : SolanaDigest) (input scratch : Array Top.E 29#usize) (prepared : Top.Prepared)
    (accepted : (eval H (body base R B other
      (.op7 (digest (fun bytes => encodeState (H bytes))) pub proof hash none input))).2=
        ok (.Ok prepared,scratch)) :
    (eval H (body base R B other
      (.op7 (digest (fun bytes => encodeState (H bytes))) pub proof hash none input))).1.length ≤ 115 ∧
    Y1Provenance base R B (digest (fun bytes => encodeState (H bytes))) pub proof hash input scratch prepared := by
  have effects := installed_effects_count base R B other H pub proof hash input
  have source : AspisS1TopPrepareSource.prepare (sourceOps base R B)
      (digest (fun bytes => encodeState (H bytes))) pub proof hash none input=ok (.Ok prepared,scratch) := by
    rw [effects.1] at accepted
    exact accepted
  exact ⟨effects.2,source_y1_provenance base R B _ pub proof hash input scratch prepared source⟩

#print axioms source_y1_provenance
#print axioms installed_y1_provenance
end AspisS1TopPrepareCode
