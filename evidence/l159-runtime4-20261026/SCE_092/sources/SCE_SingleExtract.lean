import SCE_ReplayExtractTransport
import SCE_SourceReadFrames
import SCE_SingleKnown
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_SingleExtract
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_Experiment F3T_TwoPass F3T_ByteCarrier F3T_CanonicalJoin
open RawRecordedOracleExtractionMassBin

/-- Replay is transported in the actual maintained extractor's failure mass,
not asserted to be present in the physical single execution's log. -/
theorem extract {F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (rust : Verifier) (physical : Physical rust)
    (raw : AcceptedVerifierJoin c D rust) (P : ByteProver) (H : Bytes → State)
    (coins : GSConcreteByteDecoderBank.RawCoins)
    (accepted : (eval H (originalWith rust (F3T_Canon.canon (lift c P)))).2.2 = true) :
    RawRecordedPublicSpendExtractorBin.extract (view (eval H (originalWith rust (F3T_Canon.canon (lift c P))))) coins =
      RawRecordedPublicSpendExtractorBin.extract (view (eval H (annotatedWith D rust (F3T_Canon.canon (lift c P))))) coins := by
  let CP := F3T_Canon.canon (lift c P)
  let v := eval H (originalWith rust CP)
  have shape : view (eval H (annotatedWith D rust CP)) =
      SCE_ReplayFrames.annotated (view v) (eval H (rust v.2.1)).1 (F3T_Charged.build D (view v)) := by
    rw [F3T_TwoPass.annotated_eval D rust (fun _ _ => physical _ _ rfl rfl)]
    rfl
  change RawRecordedPublicSpendExtractorBin.extract (view v) coins =
    RawRecordedPublicSpendExtractorBin.extract (view (eval H (annotatedWith D rust CP))) coins
  rw [shape]
  have cuts := SCE_SourceReadFrames.frames c D rust physical raw P H accepted
  exact SCE_ReplayExtractTransport.extract (view v) (eval H (rust v.2.1)).1
    (F3T_Charged.build D (view v)) H (SCE_SingleKnown.consistent rust CP H)
    (SCE_SingleKnown.known rust CP H) cuts.1 cuts.2.1 cuts.2.2 coins

#print axioms extract
end AspisR1.SCE_SingleExtract
end
