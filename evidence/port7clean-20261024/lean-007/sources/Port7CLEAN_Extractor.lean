import Port7CLEAN_Carrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port7CLEAN_Extractor
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4 OraclePortRuntimeBindingC7
open Port1_StoredCarrier Port6AUTH_SourceCut Port6AUTH_Prefix
attribute [local irreducible] originalWith canon lift source LiteralByteProtocol.protocol
  FS2.Protocol.transcript BinCompiledRunWordStability.wordsFromRun
  RawCutWordsFromRunExecutableBin.wordsFromRun

/-- The extractor's executable recovery equals the first source builder and
fixes the full source proof. Uses actual stored parsing and sampler read
provenance, without terminal Checks, acceptance or a classifier premise. -/
theorem fixed (D : LiteralByteProtocol.Decoder) (rust : Verifier) (P : ByteProver)
    (H : Bytes → State) (p : OraclePortCompactDraft.Parsed)
    (parsed : OraclePortCompactDraft.parse (first rust P H).2.1.stored=some p)
    (contains : ∀ a, Read (eval H (RawCutProverCompiler.verifier D (fun _ _ => false)
      (first rust P H).2.1.statement (first rust P H).2.1.proof)).1 a → Read (first rust P H).1 a) :
    RawCutWordsFromRunExecutableBin.wordsFromRun (eval H (source D rust P))=build D (view (first rust P H)) ∧
    RawCutTranscriptRun.proof (RawCutWordsFromRunExecutableBin.wordsFromRun (eval H (source D rust P)))
      (eval H (source D rust P)).2.1.2=(eval H (source D rust P)).2.1.2 := by
  let before := first rust P H
  let run := eval H (source D rust P)
  have pf : run.2.1.2=RawCutTranscriptRun.proof (build D (view before)) before.2.1.proof := by
    simp only [run,before,source_eval,OraclePortFrozen2Join.annotatedWith_eval,view,enrich]
  have valid : RawCutWordsFromRunExecutableBin.ValidPrefix run := by
    intro row bound
    rw [pf]
    apply (OraclePortSemanticObservationsC6.valid_enrich _ _ _).2
    rw [Port7CLEAN_Carrier.first_proof rust P H p parsed]
    exact Port7CLEAN_Carrier.parsed_valid p row (by omega)
  have words : RawCutWordsFromRunExecutableBin.wordsFromRun run=build D (view before) :=
    (RawCutWordsFromRunExecutableBin.wordsFromRun_eq_buildWords D run valid).trans
      (Port6AUTH_WordStability.words_stable D rust P H contains)
  refine ⟨words,?_⟩
  rw [words,pf]
  funext row
  cases before.2.1.proof row <;> rfl

#print axioms fixed
end AspisR1.Port7CLEAN_Extractor
end
