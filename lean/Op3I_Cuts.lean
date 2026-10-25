import Op3I_Install
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.Op3I_Cuts
open AspisR1CurrentCaller S2W_NativeConsolidation
open Op3I_Install

/-- The header projection used by frozen2 parseReached. The frozen model has
no separate returned Variant; this names its successful S2 header component. -/
def frozenHeader (stored : AspisV8R19.DuplexFrames.Bytes) : Option transport.Variant :=
  if OraclePortHeader.accepts stored then some .S2 else none

/-- The same f,s and stored proof carrier from accepted_pair_claims. No second
execution, newly selected cut or whole-parser success is a premise. -/
theorem same_cut_header (adapterOps : AdapterRw.Ops) (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (std : ClaimsUnrolledFinish.StdCalls)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts)
    (saved : alloc.vec.Vec U8) (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (ClaimsUnrolledSdk.sdkOps adapterOps (install ops) B std)
      accounts1 accounts2 saved f s) :
    (RowShape_InstalledSlots.verifierOps (install ops) B std).op3 f.proof = ok (.Ok .S2) ∧
    sourceBody f.proof = ok (.Ok .S2) ∧
    OraclePortHeader.accepts (MultiproofConeCanonical.bytesOf f.proof.val) = true ∧
    frozenHeader (MultiproofConeCanonical.bytesOf f.proof.val) = some .S2 := by
  have tx := AspisS6CurrentFirstInstallation.current_success
    (RowShape_InstalledSlots.verifierOps (install ops) B std) _
    f.semantic f.pub f.proof f.split () saved
    (AspisS6CurrentStage1CodecJoin.first_success
      (ClaimsUnrolledSdk.sdkOps adapterOps (install ops) B std)
      f.semantic f.pub f.proof f.split saved cuts.first)
  obtain ⟨_,variant,zero,prepared,scratch,shape,_⟩ :=
    Tx1Reachability.tx1_success _ _ _ f.pub f.proof f.split () saved tx
  have call : sourceBody f.proof = ok (.Ok variant) := shape
  obtain ⟨rfl,header⟩ := header_of_success f.proof variant call
  exact ⟨shape,call,header,by simp only [frozenHeader,header,if_true]⟩

/-- Explicit remaining parser obligations, on these same stored bytes. This
lemma proves no source scan/op4, semanticRows or transcript alignment law. -/
theorem full_parse_of_remaining (proof : Slice U8) (variant : transport.Variant)
    (headerCall : sourceBody proof = ok (.Ok variant))
    (semantic : List AspisV8R19.DuplexFrames.Bytes)
    (tr : RawCutTranscriptRun.ErasedPrefix)
    (scan : OraclePortCompactDraft.scan (MultiproofConeCanonical.bytesOf proof.val))
    (rows : OraclePortCompactDraft.semanticRows 27 0
      (OraclePortCompactDraft.slice (MultiproofConeCanonical.bytesOf proof.val) 48 6983) = some semantic)
    (aligned : OraclePortCompactDraft.Aligned
      ⟨MultiproofConeCanonical.bytesOf proof.val,semantic⟩ tr) :
    OraclePortStoredParserC4.parseReached (MultiproofConeCanonical.bytesOf proof.val) tr =
      some ⟨MultiproofConeCanonical.bytesOf proof.val,semantic⟩ :=
  OraclePortStoredParserC4.parse_of_parts _ _ _
    (header_of_success proof variant headerCall).2 scan rows aligned

#print axioms same_cut_header
#print axioms full_parse_of_remaining
end AspisR1.Op3I_Cuts
end
