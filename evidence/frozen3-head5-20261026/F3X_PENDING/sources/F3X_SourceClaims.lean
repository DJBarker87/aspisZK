import F3X_Cost
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3X_SourceClaims
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleResampling
open F3T_Experiment F3T_TwoPass F3T_ByteCarrier
open RawExtractorCostComposedV2 (Coins)

def Claims {F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder)
    (hashv : SdkC_Source.Parts → Aeneas.Std.Result SdkC_Source.Digest)
    (P : ByteProver) (Q : Nat)
    (select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs) : Prop :=
    ∀ (H : Bytes → State),
    (eval H (annotatedWith D (F3T_Installed.source c hashv) (F3T_Canon.canon (lift c P)))).2.2=true →
    mean (fun coins : Coins=>((ActualCostedExtractorM10.extractor.eval
      (view (eval H (annotatedWith D (F3T_Installed.source c hashv) (F3T_Canon.canon (lift c P))))) coins).2.total : Rat))≤
      ((CostedAllocationLedgerM10.params (Q+1161)).attemptBudget : Rat) ∨
    BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
      (eval H (Hiq_RecordedJoint.program (F3X_Account.program c hashv P) F3X_Projection.project select))

end AspisR1.F3X_SourceClaims
end
