import F3U_Recovered
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_ExtractorOrCollision
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_Experiment F3T_Charged F3T_TwoPass F3T_ByteCarrier F3U_CollisionJoin

theorem extractor {F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (rust : Verifier) (physical : F3T_CanonicalJoin.Physical rust)
    (bad : Exception) (join : Join c D rust bad) (P : ByteProver) (H : Bytes → State)
    (accepted : (eval H (annotatedWith D rust (F3T_Canon.canon (lift c P)))).2.2=true) :
    (∀ coins : GSConcreteByteDecoderBank.RawCoins,
      RawRecordedPublicSpendExtractorBin.extract (view (eval H (annotatedWith D rust (F3T_Canon.canon (lift c P))))) coins=
      RawRecordedPublicSpendExtractorBin.extract (view (eval H (recorded D (build D) (F3T_Canon.canon (lift c P))))) coins) ∨
    bad H (eval H P).2.publicBytes (eval H P).2.stored := by
  rcases F3U_Recovered.inputs_or_collision c D rust physical bad join P H accepted with agreement | collision
  · left
    intro coins
    exact OraclePortRefineJoin.extractor_eq_of_recovered_inputs _ _ agreement coins
  · exact Or.inr collision

#print axioms extractor
end AspisR1.F3U_ExtractorOrCollision
end
