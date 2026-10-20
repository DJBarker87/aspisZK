import DecoderInstanceBoundary
import BinCompiledRunWordStability

set_option autoImplicit false
noncomputable section
namespace AspisR1.DecoderInstanceBoundaryBin
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open RawCutTranscriptRun RawCutProverCompiler LiteralAcceptanceTerminal

abbrev annotatedRun (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (H : Bytes → State) :=
  eval H (experiment (compiled D d (BinCompiledRunWordStability.wordsFromRun D) P) (verifier D d))

abbrev compiledPublic (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (H : Bytes → State) :=
  (annotatedRun D d P H).2.1.1

abbrev compiledRows (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (H : Bytes → State) :=
  ((LiteralByteProtocol.protocol D).transcript H (compiledPublic D d P H)
    (annotatedRun D d P H).2.1.2 33).rounds

/-- Reader-derived fields on the exact M9 transcript. Missing lemma groups:
AcceptedSourceToCompiledRows supplies hmatching/h31/h32/hv31/hv32/hq;
AcceptedPairing supplies hpairing; AuthenticatedFirstMatch supplies hfirst;
RestoredAccumulatorClosedSum supplies haccum; LiteralSemanticEndpoint supplies
hsemantic. R2/R5/stage-2 first facts alone do not supply these implications. -/
theorem hchecks_deployed_partial
    (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover)
    (H : Bytes → State)
    (decoded : R0P.Public SemanticPublicWire.M31)
    (data : MatchingSupport.Data E)
    (hpublic : SemanticPublicWire.parsePublic (compiledPublic D d P H).pubBytes = some decoded)
    (hmatching : LiteralMatchingData.read (compiledRows D d P H) = some data)
    (hpairing : LiteralPairingChecks.checks (compiledRows D d P H))
    (m31 : LiteralTranscript.Message) (queryBytes : List Nat) (state31 : State)
    (m32 : LiteralTranscript.Message) (rho : E) (state32 : State)
    (h31 : (compiledRows D d P H)[31]? = some (m31,
      (TranscriptView.Value.queries (.ok queryBytes), state31)))
    (h32 : (compiledRows D d P H)[32]? = some (m32,
      (TranscriptView.Value.ordinary rho, state32)))
    (hv31 : LiteralTranscript.valid 31 m31)
    (hv32 : LiteralTranscript.valid 32 m32)
    (hq : queryBytes.Nodup ∧ queryBytes.length = 22 ∧
      ∀ x ∈ queryBytes, x < 262144)
    (hfirst : ∀ q : Fin 22 → Fin 262144,
      LiteralQueryRead.decode queryBytes = some q →
      ∀ j, MatchingSupport.match0 data (q j))
    (haccum : ∀ q : Fin 22 → Fin 262144,
      LiteralQueryRead.decode queryBytes = some q →
      HchecksAccumulator.ClosedSum LiteralOpeningView.eK data q
        (SelectedChallengeMap.rhoOf rho))
    (hsemantic : HchecksReaderComposition.SemanticEndpoint decoded (compiledRows D d P H) data) :
    Nonempty (Checks (compiledPublic D d P H) (compiledRows D d P H)) := by
  exact HchecksReaderComposition.hchecks_partial
    (compiledPublic D d P H) (compiledRows D d P H) decoded data
    hpublic hmatching hpairing m31 queryBytes state31 m32 rho state32
    h31 h32 hv31 hv32 hq hfirst haccum hsemantic

#print axioms hchecks_deployed_partial
end AspisR1.DecoderInstanceBoundaryBin
end
