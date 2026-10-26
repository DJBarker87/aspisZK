import F3T_AcceptedTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_Recovered
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_Experiment F3T_Charged F3T_TwoPass F3T_AcceptedTransport

theorem inputs (D : LiteralByteProtocol.Decoder) (rust : Verifier)
    (inv : AnnotationInvariant rust) (join : RawJoin D rust) (P : Prover) (H : Bytes → State)
    (ha : (eval H (annotatedWith D rust P)).2.2=true) :
    OraclePortRefineJoin.RecoveredInputAgreement
      (view (eval H (annotatedWith D rust P)))
      (view (eval H (recorded D (build D) P))) := by
  rw [annotated_eq D rust inv join P H ha]
  exact ⟨rfl,rfl,rfl⟩

theorem extractor (D : LiteralByteProtocol.Decoder) (rust : Verifier)
    (inv : AnnotationInvariant rust) (join : RawJoin D rust) (P : Prover) (H : Bytes → State)
    (ha : (eval H (annotatedWith D rust P)).2.2=true)
    (coins : GSConcreteByteDecoderBank.RawCoins) :
    RawRecordedPublicSpendExtractorBin.extract (view (eval H (annotatedWith D rust P))) coins=
      RawRecordedPublicSpendExtractorBin.extract (view (eval H (recorded D (build D) P))) coins :=
  OraclePortRefineJoin.extractor_eq_of_recovered_inputs _ _ (inputs D rust inv join P H ha) coins

#print axioms inputs
#print axioms extractor
end AspisR1.F3T_Recovered
end
